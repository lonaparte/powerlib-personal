# 01 — 完整走完验证流程的全部证明（审计版）

> 本目录只收**完整走完同一条形式化流程**的证明产物。
> 进入条件(机械可查,无例外):
> - `.kyx`:有 Problem 块(遵循 `formalization/Conventions.md`)+ 有 Tactic + 配套 `.kyx.kyp` 含 `\qed`,
>   且在**入目录当日全部 104 个文件串行 fresh 重跑**,fresh `\qed` 与仓库 `.kyp` 逐一一致(104/104,无空壳)。
> - `.lean`:Lean 4.14.0 实际编译 EXIT=0、无 `sorry`,`#print axioms` 仅 `[propext, Quot.sound]`。
> - 移动后又从**新位置**抽样重证(每桶一个 + Lean 重编),确认位置无关。
>
> **不在本目录的**(留在 `formalization/archive/phdae/`):10 个 OPEN(有 Tactic 但 Z3 后端闭合不了,
> 文件头已注明原因)、4 个 conjecture(仅 Problem)、2 个探索性 Lean(`Dynamics.lean` 含 sorry、
> `PHDAE.lean` 为卡点记录)。它们没有走完流程,如实分开存放。

## 流程(每个文件都经过的四层)

1. **约定层**:记号/编码遵循 `formalization/Conventions.md`(sin/cos 用 s,c+圆约束 ODE 编码;H 不含 1/2)。
2. **实例证明层**:KeYmaera X 5.1.2(Z3 后端),`java -jar keymaerax.jar -prove FILE.kyx`;
   唯一判据 = `.kyp` 含 `\qed`;一律**串行**运行(并行会产生空壳 `.kyp`)。
3. **交叉验证层**:sympy 精确核 Lie 导数/witness;fsolve 算能垒;负对照(故意改错的变体必须 FAIL)。
4. **元层一般化**:dL 无法对 ∀N/∀拓扑量化的跨实例规律,在 `lean/` 用纯 Lean 4 机器证明。

## 目录与内容

| 子目录 | 文件 | 内容 |
|---|---|---|
| `smib/` | 13 对 | 单机 SMIB 全栈:守恒、稳定域 {H<4K}、被动 Lyapunov、渐近(实例+参数化代数条件)、负阻尼失稳、带载平衡、失步 |
| `two_machine/` | 55 对 | 两机全栈:被动不变/守恒/∀ε∃δ(H 度量+分量)/能量恒等式/稳定域/渐近(实例)/必要性(d0,dneg,k0)/鞍点失稳/Schur/Level C(M1,M3,恒等式)/**D₂<0 混号完整闭合**(theorem_ph_bridge 系列、theorem_ph_complete)/不可能性(impossibility_ph_linear, gap_no_ph_lyapunov)/LaSalle 步骤等 |
| `three_machine/` | 17 对 | 三机(链 1-2-3 + 三角环):被动全栈、分量 ∀ε∃δ(δ=ε/(4K+3))、必要性/失稳 4 件套(k0 强版、dneg、鞍点能垒、鞍点力符号)、D₂<0 线性化(d<19/100)与大信号下降、**box descent(凸组合+抽象符号装配)**、环拓扑对照({H<8K});含通用引理 `lemma_sign_assembly`、三节点 DAE |
| `four_machine/` | 19 对 | 四机 **6 种连通拓扑穷举**(链/星/paw/环/菱形/K4):每种被动不变 {H<1} + 稳定域(阈值=数值最低鞍点 4K/4K/4K/8K/8K/12K);链上另有守恒、H-度量 ∀ε∃δ、能量恒等式、必要性/失稳 4 件套 |
| `lean/` | 2 + toolchain | `PHGeneral.lean`:**任意维任意拓扑**的 pH 能量平衡核心(gᵀJg=0、率=−ΣDᵢgᵢ²、同号三情形 passive/conservative/antipassive)+ 混号边界说明;`PHEnergyBalance.lean`:固定 2 维代数核心(历史版) |

合计:**104 个 KeYmaera X 机器验证证明 + 2 个 Lean 编译验证文件**。

## 复现

```bash
# KeYmaera X(任一 .kyx;串行!)
java -jar keymaerax.jar -prove 01/three_machine/parametric_3machine.kyx -out /tmp/out.kyp
grep -cF '\qed' /tmp/out.kyp     # 1 = PROVED

# Lean(toolchain 见 lean/lean-toolchain: leanprover/lean4:v4.14.0)
lean 01/lean/PHGeneral.lean       # 退出码 0,#print axioms 仅 propext/Quot.sound
```

## 诚实标注(与文件头一致)

- 稳定域文件证明的形式内容是"{H<c} 对**任意** c 正不变"(dI 只用 H 单调);
  能垒值 4K/8K/12K 是**数值**最低鞍点(fsolve),非形式紧界——各文件头已写明。
- 渐近稳定为实例级(K=D=1 等);一般参数版受 existsR witness/SOS 限制,属 OPEN,不在本目录。
- Lean 元层只覆盖"同号阻尼"(全≥0/全=0/全≤0)可统一推广的 A 类;混号(如 D₂<0 中间机)
  需逐拓扑设计增广 V,无统一定理(见 `PHGeneral.lean` 头部 SIGN-MIXED 节)。
