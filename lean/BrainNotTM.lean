/-
================================================================================
人类大脑非图灵机论证 —— Lean 4 形式化
================================================================================

对应原文：《推演：大脑是非图灵机》
（本仓库根目录的《推演：大脑是非图灵机.md》）

【定义层的推演（从公认基本定义出发）】

公认：**算法 = 有限、确定、可机械执行的步骤序列**。

1. "步骤序列"的含义里包含步骤结构：什么算一步、如何连接、什么算有效、
   何时停止——即约束空间（原文第一步的概念分析）。
   ⇒ "预设"（Presupposes）= 过程与其步骤结构的关系。

2. "确定"的含义（前提 P）：不是"渐进确定"、不是"无限逼近的极限"
   ——确定性必须"落地"（有限），不能悬空于无限回溯。
   ⇒ "确定"（Determined）= 上游链可及（Acc dep）。

3. "算法要确定性，确定性的前提就是得有一个确定的约束空间"。
   反证：假设约束空间不确定——则算法不可能确定（确定的执行需要
   确定的规则结构）；算法不确定则不存在（"确定"是算法的定义性
   要求）——与"算法存在"矛盾。故约束空间必须确定。
   ⇒ "算法"（IsAlgorithm）= 有**确定**步骤结构（预设空间）的过程。
   ⇒ "算法以确定的约束空间为存在条件"是定义展开——无需假设。
   ⇒ 起点：世界上存在算法。

【实质前提对照表（5 条）】
| 假设            | 原文对应         | 一句话                                  |
|-----------------|------------------|-----------------------------------------|
| (∃ p, IsAlgorithm p) | （事实前提）| 世界上存在算法（起点）                   |
| source_exists   | 第五步           | 确定的约束空间必由某过程生成             |
| in_or_input     | 第八步           | 非算法过程：颅内 / 颅外输入，二分穷尽    |
| input_is_info   | F2               | 颅外只能输入信息                         |
| nonalg_not_info | 第八步           | 非算法过程不是信息                       |

【与 F1 的关系】
原文 F1（"约束生成发生了"）→ 形式化为"存在算法"：
由定义（算法 = 有确定步骤结构的过程），起点直接给出确定空间 s₀，开启回溯链。
F1 作为"经验锚定"的哲学作用不变（起点仍是实际事实），但它不是逻辑上必需的。

【技术说明】
- 纯 Lean 核心库（Init），无外部依赖（不需要 Mathlib）
- 使用经典逻辑（by_cases 二分）：依赖 Lean 的 Classical 公理（见文件末尾）
- 论证打包为 `World` 结构（论域 + 概念谓词）；定理为参数化形式
  （前提作为显式假设，不引入全局 axiom）

【定理清单】
1. World.non_algo_process_exists   —— 存在非算法过程（阶段一，核心）
2. World.non_algo_in_brain         —— 非算法过程在大脑内（阶段二）
3. World.not_turing_machine        —— 推论
4. World.brain_not_turing_machine  —— 端到端：完整论证的最终结论
-/

-- ============================================================================
-- 论证框架（论域 + 原始概念谓词）
-- ============================================================================

/-- 论证涉及的框架：论域与概念。

    （形式化的是推理，不是概念内容——谓词均为未定义的占位符。） -/
structure World where
  -- 论域
  Process : Type
  ConstraintSpace : Type
  -- 原始概念（阶段一）
  Presupposes : Process → ConstraintSpace → Prop
  Generates : Process → ConstraintSpace → Prop
  -- 原始概念（阶段二）
  -- 在颅内执行 / 颅外输入——二分穷尽。论域：约束生成链涉及的过程——
  -- 它们要么在颅内执行、要么从颅外（以输入形式）进入。
  -- （与大脑无关的颅外执行过程不在论域——不进入本大脑的约束生成链。）
  InBrain : Process → Prop
  SkullInput : Process → Prop
  IsInformation : Process → Prop

namespace World

-- ============================================================================
-- 定义层（从公认基本定义推演——见文件头）
-- ============================================================================

/-- 上游：直接上游（某过程预设 a 且生成 b）的传递闭包——"依赖链"的精确含义。

    这是原文第七步(1)的精确化："确定性传递"的每一步结构。 -/
abbrev dep (W : World) (a b : W.ConstraintSpace) : Prop :=
  Relation.TransGen (fun x y => ∃ p : W.Process, W.Presupposes p x ∧ W.Generates p y) a b

/-- 确定：上游链可及（有限）。

    从"确定"的含义推演（前提 P）："约束空间的确定性是算法存在的前提……
    它不能是'渐进确定'或'无限逼近的极限'"——无限回溯意味着确定性
    无处落地；"确定"即"有尽头"。 -/
abbrev Determined (W : World) (s : W.ConstraintSpace) : Prop := Acc W.dep s

/-- 算法：有**确定的**步骤结构（预设空间）的过程。

    从公认定义推演：算法 = 有限、**确定**、可机械执行的步骤序列。

    第③步推演（反证）：假设约束空间不确定——那么算法不可能确定
    （确定的执行需要确定的规则结构）；算法不确定则不存在（"确定"
    是算法的定义性要求）——与"算法存在"矛盾。故约束空间必须确定。

    因此"算法以确定的约束空间为存在条件"是定义展开，无需假设。 -/
abbrev IsAlgorithm (W : World) (p : W.Process) : Prop :=
  ∃ s, W.Presupposes p s ∧ W.Determined s

-- ============================================================================
-- 阶段一：存在非算法过程（对应原文第一~七步）
-- ============================================================================

/-- 定理 1：存在非算法过程。

    证明策略：对可及性（Acc）归纳（构造性——不依赖反证）。

    起点：世界上存在算法——由定义展开（算法 = 有确定步骤结构的过程），
    给出起点空间 s₀（无需 F1"约束生成发生了"）。

    核心链条：确定空间 → 生成者（第五步）→ 若生成者是算法，由定义它
    有更上游的确定空间 s'（预设）→ dep s' x → 可及性（Acc 的结构）
    保证递归良基 → 链必终止于非算法生成者。 -/
theorem non_algo_process_exists (W : World)
    -- 起点：世界上存在算法
    (h_algo : ∃ p, W.IsAlgorithm p)
    -- 第五步：确定的约束空间必由某过程生成（大脑语境）
    (source_exists : ∀ s, W.Determined s → ∃ p, W.Generates p s) :
    ∃ p, ¬ W.IsAlgorithm p := by
  -- 起点：取算法 p₀ → 定义展开：它有确定的约束空间 s₀
  obtain ⟨p₀, s₀, _, hDet₀⟩ := h_algo
  -- 核心引理：每个确定空间要么找到非算法生成者，要么回溯到上游
  have key : ∀ s, W.Determined s → ∃ p, ¬ W.IsAlgorithm p :=
    fun s hAcc => hAcc.rec (motive := fun _ _ => ∃ p, ¬ W.IsAlgorithm p)
      (fun x hx ih => by
        -- x 确定（可及）→ 生成者 p（第五步）
        obtain ⟨p, hGen⟩ := source_exists x (Acc.intro x hx)
        by_cases hp : W.IsAlgorithm p
        · -- p 是算法 → 定义展开：p 有更上游的确定空间 s'
          obtain ⟨s', hPre, _⟩ := hp
          have hDep : W.dep s' x := Relation.TransGen.single ⟨p, hPre, hGen⟩
          -- 继续回溯（s' 的可及性由 Acc 结构自动给出）
          exact ih s' hDep
        · -- p 不是算法 → 找到结论
          exact ⟨p, hp⟩)
  -- 起点 s₀ 确定 → 回溯链必终止于非算法过程
  exact key s₀ hDet₀

-- ============================================================================
-- 阶段二：非算法过程在大脑内（对应原文第八步）
-- ============================================================================

/-- 定理 2：非算法过程在大脑内部。

    证明策略：对定理 1 给出的非算法过程应用二分穷尽——
    它要么在颅内执行、要么是颅外输入；若是颅外输入，则它是信息（F2），
    与"非算法过程不是信息"矛盾。故在颅内。 -/
theorem non_algo_in_brain (W : World)
    -- 阶段一的结论（可由定理 1 提供，也可来自其他来源）
    (h_nonalg : ∃ p, ¬ W.IsAlgorithm p)
    -- 第八步：二分穷尽（非算法过程要么在颅内、要么是颅外输入——
    -- 论域内穷尽：与大脑无关的颅外过程不在论域）
    (in_or_input : ∀ p, ¬ W.IsAlgorithm p → W.InBrain p ∨ W.SkullInput p)
    -- F2：颅外只能输入信息
    (input_is_info : ∀ p, W.SkullInput p → W.IsInformation p)
    -- 第八步：非算法过程不是信息（它是执行过程）
    (nonalg_not_info : ∀ p, ¬ W.IsAlgorithm p → ¬ W.IsInformation p) :
    ∃ p, W.InBrain p ∧ ¬ W.IsAlgorithm p := by
  obtain ⟨p, hNot⟩ := h_nonalg
  have hIn : W.InBrain p := by
    rcases in_or_input p hNot with h | h
    · exact h
    · exact absurd (input_is_info p h) (nonalg_not_info p hNot)
  exact ⟨p, hIn, hNot⟩

-- ============================================================================
-- 图灵机推论
-- ============================================================================

/-- "系统是图灵机"的定义：其所有过程都是算法。

    （图灵机 = 只能执行算法过程的理想计算模型——原文定义） -/
abbrev IsTuringMachine (W : World) : Prop := ∀ p : W.Process, W.IsAlgorithm p

/-- 推论：若存在非算法过程，则系统不是图灵机。 -/
theorem not_turing_machine (W : World)
    (h : ∃ p, ¬ W.IsAlgorithm p) :
    ¬ W.IsTuringMachine := by
  intro hTM
  obtain ⟨p, hNot⟩ := h
  exact hNot (hTM p)

-- ============================================================================
-- 端到端：完整论证的最终结论
-- ============================================================================

/-- 最终结论：大脑不是图灵机。

    前提 = 阶段一（2 条）+ 阶段二（3 条）——全部对应原文的实质前提
    （第五步锚定/F2/Q 与第八步）。结论由 Lean 内核验证。 -/
theorem brain_not_turing_machine (W : World)
    -- 阶段一
    (h_algo : ∃ p, W.IsAlgorithm p)
    (source_exists : ∀ s, W.Determined s → ∃ p, W.Generates p s)
    -- 阶段二
    (in_or_input : ∀ p, ¬ W.IsAlgorithm p → W.InBrain p ∨ W.SkullInput p)
    (input_is_info : ∀ p, W.SkullInput p → W.IsInformation p)
    (nonalg_not_info : ∀ p, ¬ W.IsAlgorithm p → ¬ W.IsInformation p) :
    ¬ W.IsTuringMachine := by
  have h1 : ∃ p, ¬ W.IsAlgorithm p :=
    W.non_algo_process_exists h_algo source_exists
  have h2 : ∃ p, W.InBrain p ∧ ¬ W.IsAlgorithm p :=
    W.non_algo_in_brain h1 in_or_input input_is_info nonalg_not_info
  obtain ⟨p, _, hNot⟩ := h2
  exact W.not_turing_machine ⟨p, hNot⟩

end World

-- ============================================================================
-- 合法性验证：推演概念可展开为更根本的概念（保守扩展——不引入新符号）
-- ============================================================================

-- 上游 = 生成-预设步的传递闭包（展开即恒等）
example (W : World) (a b : W.ConstraintSpace) :
    W.dep a b ↔
      Relation.TransGen (fun x y => ∃ p : W.Process, W.Presupposes p x ∧ W.Generates p y) a b :=
  Iff.rfl

-- 确定 = 可及（展开即恒等）
example (W : World) (s : W.ConstraintSpace) :
    W.Determined s ↔ Acc W.dep s :=
  Iff.rfl

-- 算法 = 有确定步骤结构（展开即恒等）
example (W : World) (p : W.Process) :
    W.IsAlgorithm p ↔ ∃ s, W.Presupposes p s ∧ W.Determined s :=
  Iff.rfl

-- 图灵机 = 所有过程都是算法（展开即恒等）
example (W : World) :
    W.IsTuringMachine ↔ ∀ p : W.Process, W.IsAlgorithm p :=
  Iff.rfl

-- ============================================================================
-- 验证：公理依赖自检（运行 lean 编译时打印）
-- ============================================================================

-- 定理 1 依赖的公理（应为经典逻辑公理 + 无自定义公理）
#print axioms World.non_algo_process_exists
-- 端到端定理依赖的公理
#print axioms World.brain_not_turing_machine
