# 当AI助手成为安全隐患：形式化验证如何守护AI基础设施

## 从一场安全风暴说起

2025年下半年，一款名为Clawdbot的开源AI助手网关在技术社区引发了广泛关注。这个项目允许用户将Claude、GPT-4等前沿大语言模型连接到WhatsApp、Telegram、Discord、Slack等消息平台，并赋予AI执行Shell命令、浏览网页、控制智能设备等强大能力。然而，伴随着用户数量的激增，安全研究人员很快发现了一个令人不安的事实：全球超过4500个Clawdbot实例的管理控制台直接暴露在公网上，攻击者只需知道访问地址，就能查看配置数据、获取API密钥、甚至浏览用户的私密聊天记录。

这一发现揭示了AI Agent时代一个深刻的安全困境。Simon Willison在2025年7月提出了"致命三角"（Lethal Trifecta）的概念：当一个AI系统同时具备访问私密数据、暴露于不可信内容、以及对外通信的能力时，它就天然处于一个极度脆弱的位置。Clawdbot恰好是这一理论的完美例证——它连接着用户最私密的通讯渠道，处理着可能包含恶意指令的用户输入，同时拥有执行系统命令的权限。

面对这样的安全挑战，传统的测试方法显得力不从心。穷举所有可能的并发请求顺序、配置组合和攻击者行为，在计算上是不可行的。而完整的程序验证对于生产级别的TypeScript代码库来说又过于昂贵。OpenClaw团队选择了一条中间路线：使用TLA+规约语言和TLC模型检查器，对系统的安全关键属性进行形式化验证。

## OpenClaw的架构与威胁模型

在深入验证细节之前，我们需要理解OpenClaw的系统架构。如图1所示，网关作为一个持久化守护进程运行，通常部署在个人服务器或VPS上。

```
+------------------+     +-----------------+
|    Messaging     |     |  Device Nodes   |
|    Channels      |     |  (macOS, iOS,   |
|   (WhatsApp,     |     |   Android)      |
|  Telegram, Slack,|     |                 |
|   Discord, ...)  |     |                 |
+--------+---------+     +--------+--------+
         |                        |
         v                        v
+----------------------------------------+
|           OpenClaw Gateway             |
| +----------+ +----------+ +------+     |
| | Channel  | | Routing  | | Tool |     |
| | Adapters | | Engine   | | Exec |     |
| +----------+ +----------+ +------+     |
| +----------+ +----------+ +------+     |
| | Pairing  | | Session  | | Auth |     |
| | Store    | | Manager  | | Gate |     |
| +----------+ +----------+ +------+     |
+----------------------------------------+
         |
         v
+------------------+
|   AI Model APIs  |
|   (Anthropic,    |
|   OpenAI, ...)   |
+------------------+

图1: OpenClaw网关架构
```

系统包含六个核心组件。Channel Adapters负责与各消息平台对接，处理平台特定的认证逻辑。Routing Engine根据频道、发送者身份和线程上下文决定消息应该路由到哪个Agent和会话。Session Manager维护对话状态，确保不同用户之间的会话隔离。Tool Execution将工具调用分发到本地Shell、浏览器自动化或远程设备节点，同时执行授权策略。Pairing Store管理允许发送私信的发送者白名单，以及新联系人的配对协议。Auth Gate处理网关自身的认证。

OpenClaw的安全设计基于四个核心假设。第一，所有入站消息都不可信，任何连接平台上的用户都可能是恶意的或已被攻陷的。第二，提示注入一定会发生，语言模型可能被操纵尝试执行未授权的操作。第三，系统为单用户设计，目标是保护运营者的数据和系统，而非提供多租户隔离。第四，物理安全被假定为可靠，主机和本地网络是可信的，远程攻击是主要威胁。

基于这些假设，安全架构创建了硬边界来限制即使语言模型被操纵时的损害范围：未知发送者必须完成配对协议才能接触助手；工具调用在到达模型之前会被策略层过滤；危险操作需要明确的人工批准；会话隔离防止跨用户的上下文泄露。

## 六类安全属性的形式化

研究团队识别并形式化了六类安全属性，每类都由多个TLA+规约来验证。

第一类是网关认证（P1）。当网关绑定到非回环地址而没有启用认证时，攻击者可以连接并发出命令。当认证开启时，没有有效凭证的连接必须在处理任何命令之前被拒绝。在反向代理后运行时，网关只能信任来自配置的trustedProxies列表中IP的X-Forwarded-For头，以防止IP欺骗。

第二类是私信配对和白名单（P2）。配对请求必须在配置的TTL后过期，批准过期的请求不应产生任何效果。每个频道同时待处理的配对请求数量必须有上限，以防止通过请求洪泛进行拒绝服务攻击。并发的配对批准不能损坏白名单存储，文件锁定必须确保原子性。批准同一发送者两次不应创建重复的白名单条目。

第三类是会话隔离（P3）。两个没有明确身份链接的对等方不能共享会话密钥，以防止上下文泄露。身份链接必须满足传递性，如果A链接到B，B链接到C，那么A也链接到C。每频道的dmScope设置必须覆盖全局默认值。

第四类是工具授权（P4）。如果任何策略层拒绝一个工具，后续层不能重新启用它，策略评估是单调递减的。提升权限的工具访问需要全局tools.elevated标志和代理特定的agents[].tools.elevated标志同时开启，使用OR逻辑会是一个安全漏洞。工具组简写（如group:memory）必须精确展开为文档中记载的工具集，不多不少。

第五类是入口门控（P5）。在配置为需要@提及的群聊中，未授权的发送者不能通过斜杠命令或特殊消息格式绕过该要求。Webhook重试不能导致消息被重复处理，每个事件ID最多处理一次。

第六类是远程执行审批（P6）。需要审批的命令在处于pending状态时不能执行。审批必须绑定到特定的请求ID，以防止重放攻击，即旧的审批授权新的请求。只有在平台默认值并上额外允许再减去拒绝列表的交集中的命令才能执行。

## 绿色/红色测试范式

形式化规约面临一个根本挑战：如何确保不变量不是"空洞为真"（vacuously true）——因为规约过于限制性而无法到达有趣的状态。研究团队通过绿色/红色测试来解决这个问题。

绿色模型（Green Model）是预期通过TLC验证的，所有指定的不变量应该在所有可达状态中成立。红色模型（Red Model）是绿色模型的变体，故意注入一个bug，TLC预期会找到一个显示不变量违反的反例轨迹。

以工具策略优先级规约为例。正确的实现是ApplyLayer先与Allow进行交集运算，再减去Deny：

```
ApplyLayer(allowed, i) == (allowed ∩ Allow(i)) \ Deny(i)
```

红色变体BadAllowOverrides则错误地在移除Deny之后进行Allow的并集运算：

```
ApplyLayerBad(allowed, i) == ((allowed \ Deny(i)) ∪ Allow(i))
```

在这种错误的公式下，一个在第2层被拒绝的工具如果出现在Allow3中可以被重新启用。TLC找到了一个反例，其中memory_get属于Deny2但也属于Allow4，显示它错误地出现在FinalAllowedBad中。

红色模型服务于三个目的。首先是非空洞性：如果TLC在红色模型中找不到反例，说明不变量可能太弱。其次是文档化：反例轨迹记录了bug如何表现。第三是回归检测：如果红色模型开始通过验证，说明规约已经弱化。

表1展示了部分绿色/红色模型对：

| 属性 | 绿色模型 | 红色模型（Bug） |
|------|----------|-----------------|
| 网关认证 | GatewayExposureV2 | ..._BadNoAuth |
| 配对上限 | PairingConcurrent | ..._BadAtomic |
| 拒绝优先 | ToolPolicyPrecedence | ..._BadAllowOverrides |
| 提升权限门控 | ElevatedGating | ..._BadOr |
| 会话隔离 | RoutingIsolation | ..._BadAlwaysMain |
| 审批令牌 | ApprovalsToken | ..._BadReplay |

## 深入案例：审批重放漏洞

NodesPipelineHarness规约是最复杂的模型，将多个安全检查组合成一个端到端的管道。它跟踪四个状态变量：inbox（待处理的执行请求）、executed（带元数据的执行轨迹）、approvalState（pending/approved/denied）和approvedRid（绑定到审批的请求ID）。

关键洞察是审批必须绑定到特定的请求ID。执行门检查如下：

```
ApprovalOk(req) ==
  IF ~ApprovalRequired THEN TRUE
  ELSE approvalState = "approved" ∧ approvedRid = req.rid

MayExecute(req) ==
  LET isNodesRun == req.tool = NodesRunTool
      policyOk == AllowedByPolicy(req.tool)
      nodesOk == IF isNodesRun THEN
                   NodeCommandAllowlisted ∧ NodeCommandDeclared
                 ELSE TRUE
      approvalOk == IF isNodesRun THEN ApprovalOk(req) ELSE TRUE
  IN policyOk ∧ nodesOk ∧ approvalOk
```

红色变体BadReplay移除了请求ID绑定：

```
ApprovalOk(_req) ==
  IF ~ApprovalRequired THEN TRUE
  ELSE approvalState = "approved"
```

这启用了一种重放攻击：攻击者获得对良性请求r1的审批，然后提交恶意请求r2。由于只检查approvalState而不是匹配的rid，r2使用r1的审批执行。TLC在90秒内找到了这个反例。

## 发现的实际Bug

在规约开发过程中，研究团队发现了三个潜在的实现bug。

第一个是配对竞态条件。原始实现先检查待处理上限，然后在单独的操作中追加请求——这是一个经典的检查时间-使用时间（TOCTOU）漏洞。TLA+模型明确建模了这个两阶段模式：

```
BeginRequest(ch, sender) ==
  ∧ Cardinality(pending[ch]) < MaxPending  (* 检查 *)
  ∧ phase' = [phase EXCEPT ![<<ch, sender>>] = "begun"]

CommitRequest(ch, sender) ==
  ∧ phase[<<ch, sender>>] = "begun"
  ∧ pending' = [pending EXCEPT              (* 使用 *)
      ![ch] = @ ∪ {[sender |-> sender, ts |-> now]}]
```

TLC用MaxPending=1找到了以下反例：

状态1：pending[ch1] = {}，两个请求都空闲
状态2：请求s1调用BeginRequest——通过上限检查（0 < 1）
状态3：请求s2调用BeginRequest——也通过（0 < 1，pending未变）
状态4：s1提交，pending[ch1] = {s1}
状态5：s2提交，pending[ch1] = {s1, s2}——违反：2 > 1

修复需要在TypeScript实现中使用文件锁定进行原子检查-追加。这个bug本可以通过洪泛配对队列超出其预期上限来允许拒绝服务攻击。

第二个是身份链接不对称。身份链接数据结构允许不对称的条目（A→B而没有B→A），违反了预期的等价关系语义。TLA+传递性检查暴露了规范化产生不一致结果的状态。

第三个是工具组漂移。一致性提取发现group:memory在TypeScript中已扩展为包含memory_put，但形式化模型仍然只指定{memory_search, memory_get}。这会导致形式化保证与实际行为产生分歧。

## CI集成的模型检查

研究团队将TLA+验证集成到GitHub Actions中，将模型检查作为与单元测试并列的一等CI步骤。工作流程对绿色模型预期成功，对红色模型预期失败（退出码12表示发现违反）。

完整的CI验证在GitHub Actions运行器上8分钟内完成。最慢的模型（配对并发、节点管道）各自探索约8万个状态。在6个月的CI运行中，观察到零次不稳定失败。TLC在给定固定常量的情况下是确定性的；模型中的非确定性（如攻击者选择）被穷举探索而非采样。在8个月的开发中，形式化验证在两个回归到达生产环境之前捕获了它们——都涉及对策略评估顺序的细微更改，否则会违反拒绝优先的语义。

表2展示了CI验证时间分解：

| 模型类别 | 时间 | 状态数 | 深度 |
|----------|------|--------|------|
| Java/TLC设置 | 45s | - | - |
| 网关暴露（5配置） | 30s | 200 | 4 |
| 工具策略优先级 | 15s | 500 | 1 |
| 提升权限门控 | 5s | 50 | 1 |
| 配对存储（3测试套件） | 90s | 35,000 | 12 |
| 路由隔离（4测试套件） | 60s | 12,000 | 8 |
| 节点管道 | 90s | 80,000 | 15 |
| 负面模型（共7个） | 2m 45s | 不等 | - |
| **总计** | **8m** | - | - |

## 一致性提取：弥合规约与实现的鸿沟

形式化规约面临与实现分歧的风险。研究团队通过一致性提取来解决这个问题：从TypeScript源代码自动生成TLA+配置。

实现在TypeScript中定义工具组：

```typescript
const TOOL_GROUPS = {
  "group:memory": ["memory_search", "memory_get", "memory_put"],
  "group:exec": ["exec", "exec_background", "exec_interactive"],
  // ...
};
```

提取脚本解析这些定义并生成TLA+配置：

```
CONSTANTS
  GroupMemory = {"memory_search", "memory_get", "memory_put"}
  GroupExec = {"exec", "exec_background", "exec_interactive"}
```

TLA+规约然后验证建模的展开是否匹配：

```
Inv_GroupMemoryExact ==
  ExpandGroup("group:memory") = GroupMemory
```

这捕获了规约和实现之间的漂移：如果开发者向一个组添加工具而没有更新形式化模型，CI就会失败。

## 局限性与未来方向

有界验证是一个固有的局限。TLC探索由MaxPending=5或MaxQueueLen=5等常量定义的有限状态空间。只在更大规模（如1000个并发请求）才表现出来的bug会被遗漏。然而，大多数安全bug——特别是授权逻辑错误——涉及TLC可靠发现的小交互模式。

模型-实现间隙是另一个挑战。TLA+规约是抽象，不是实际的TypeScript代码。模型和实现之间翻译的bug仍然可能存在。研究团队通过一致性提取、命名对齐（如resolveGatewayAuth()对应ResolveMode）以及将规约链接到实现行号的代码注释来缓解这一问题。然而，这个间隙是根本性的，如果没有程序验证就无法完全消除。

大多数规约检查安全不变量（"坏事不会发生"）。活性属性（"好事最终会发生"）更难指定和验证。当前只包含少数几个：RetryTerminationHarness验证有界的重试尝试，MultiEventEventualEmissionHarness验证排队的事件最终发出。

研究团队正在探索几个未来方向。第一是自动规约生成，用LLM辅助将自然语言的安全声明翻译成TLA+不变量。第二是运行时验证，将TLA+规约编译为检查活流量上不变量的运行时监视器。第三是组合验证，验证模块组合是否保持安全属性。第四是密码协议集成，将授权模型与底层认证协议的ProVerif或Tamarin模型链接，提供端到端保证。

## 结语

AI助手正在获得越来越多的能力，连接到越来越多的系统。从Clawdbot/Moltbot的安全事件我们可以看到，当"简单易用的AI"与系统级能力结合时，安全问题变得格外棘手。这篇论文展示了一条实用的路径：使用轻量级形式化方法——有限状态空间上的有界模型检查——可以在实际的CI时间预算内提供有意义的安全保证。

绿色/红色测试范式解决了空洞规约这个持久性挑战，而一致性提取缓解了模型-实现漂移。当模型检查在每个PR上运行时，开发者自然会考虑更改如何影响安全属性。规约成为活的文档，反例轨迹成为安全Bug的精确说明书。

对于那些正在构建或运维AI Agent系统的团队来说，这篇论文提供了一个可操作的蓝图。多通道访问控制、会话隔离、工具授权层级、危险操作的审批工作流——这些安全属性是通用的。而形式化方法不再是象牙塔中的学术工具，而是可以切实保护用户安全的工程实践。

---

**参考资料**

Natarajan, V. (2026). Model Checking Security Properties of AI Assistant Gateways: A TLA+ Case Study of OpenClaw.

TLA+ specifications available at: https://github.com/openclaw/clawdbot-formal-models
