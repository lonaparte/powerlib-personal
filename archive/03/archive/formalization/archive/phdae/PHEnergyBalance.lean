/-
  pH 系统能量平衡的完整代数证明（纯 Lean 4，无 Mathlib）

  证明了：∇H · (J-R)∇H = -(R11·x1² + R22·x2²)

  这就是 KeYmaera X 微分不变量方法的代数核心：
  从 Lie 导数的非正性直接得出能量不增，
  不需要 ODE 解的存在性、链式法则、微积分基本定理。

  关键发现：
  1. KeYmaera X 的方法可以绕过整个 "空白中间层"
  2. pH 的能量平衡是纯代数，与 KeYmaera X 的微分不变量天然匹配
  3. 纯 Lean 4 中这个证明需要 ~30 行，Mathlib 的 ring 可缩到 1 行
-/

-- 引理 1：反对称项抵消
-- x1·(J·x2) + x2·(-(J·x1)) = 0
-- 物理含义：互联矩阵 J 不产生或消耗能量
theorem j_cancel (x1 x2 J : Int) :
    x1 * (J * x2) + x2 * (-(J * x1)) = 0 := by
  rw [Int.mul_neg]
  suffices h : x1 * (J * x2) = x2 * (J * x1) by
    rw [h, Int.add_right_neg]
  rw [← Int.mul_assoc, Int.mul_comm x1 J, Int.mul_assoc]
  rw [← Int.mul_assoc x2 J x1, Int.mul_comm x2 J, Int.mul_assoc J x2 x1]
  rw [Int.mul_comm x2 x1]

-- 引理 2：耗散项的符号
-- x1·(-(R1·x1)) + x2·(-(R2·x2)) = -(R1·x1² + R2·x2²)
-- 物理含义：耗散矩阵 R 只消耗能量
theorem r_terms (x1 x2 R1 R2 : Int) :
    x1 * (-(R1 * x1)) + x2 * (-(R2 * x2))
    = -(R1 * x1 * x1 + R2 * x2 * x2) := by
  rw [Int.mul_neg, Int.mul_neg]
  rw [← Int.mul_assoc x1 R1 x1, Int.mul_comm x1 R1, Int.mul_assoc]
  rw [← Int.mul_assoc x2 R2 x2, Int.mul_comm x2 R2, Int.mul_assoc]
  omega

-- 主定理：pH 能量平衡（Lie 导数公式）
-- ∇H · ((J-R)∇H) = -(R11·x1² + R22·x2²)
--
-- 其中 J = [[0, J12], [-J12, 0]], R = diag(R11, R22)
-- ∇H = (x1, x2)（对 H = (x1² + x2²)/2）
--
-- 这是微分不变量方法的核心：
-- 如果 R11 ≥ 0 且 R22 ≥ 0，则 Lie 导数 ≤ 0，
-- 由 dL 的微分不变量规则直接得出 H 沿任何解不增。
theorem ph_energy_balance (J12 R11 R22 x1 x2 : Int) :
    x1 * (-R11 * x1 + J12 * x2) + x2 * (-J12 * x1 + -R22 * x2)
    = -(R11 * x1 * x1 + R22 * x2 * x2) := by
  rw [show -R11 = -(R11 : Int) from rfl]
  rw [show -J12 = -(J12 : Int) from rfl]
  rw [show -R22 = -(R22 : Int) from rfl]
  rw [Int.mul_add x1, Int.mul_add x2]
  rw [Int.neg_mul R11 x1, Int.neg_mul J12 x1, Int.neg_mul R22 x2]
  rw [Int.add_assoc]
  rw [← Int.add_assoc (x1 * (J12 * x2))]
  rw [j_cancel x1 x2 J12]
  rw [Int.zero_add]
  exact r_terms x1 x2 R11 R22
