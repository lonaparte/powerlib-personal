# 03 — 分支证明审计 + 通过项归档

本目录是对**整个分支 `claude/focused-ride-Uqc6p`(96 commits)**的证明内容做一遍审计,把**通过的**(= 机器验证、公理干净的 Lean 证明)集中归档。

> **这些是副本。** 可编译的权威源在 `formalization/gfl/`(Lean 4 + Mathlib lake 工程)。
> 这里的 `.lean` **不单独编译**(彼此 + 向引擎模块有 import 依赖);**公理闸门跑在 `formalization/gfl/` 上**:`scripts/check_axioms.sh` → 当前 **146/146**,公理恰为 `[propext, Classical.choice, Quot.sound]`,无 `sorryAx`、无 `native_decide`。工程未被改动。

## 判定标准("通过"= 什么)

一条 Lean 证明**通过**当且仅当:在活跃 lake 工程里、被 `#print axioms` 闸门覆盖、且恰好依赖标准三公理、无 `sorryAx`。按此:

- **26 个活跃 GFL 模块全部通过** → 收入本目录。
- **7 个 `formalization/archive/*` + `phdae/*`**(独立的、被取代的旧工程,自带 lakefile,**不在活跃闸门里**)→ **不通过**,不收(见末尾)。

收进来的按**五步流水线**符合度分三层(都通过,层级只标方法严格度):

## 五步流水线

① 模型(sympy 推导)② 生成器(脚本机械写 Lean,杜绝手抄)③ Lean 机器证 ④ 公理闸门 ⑤ 独立数值验证(numpy/scipy,独立于生成路径)。环境:Lean `v4.31.0-rc1` + Mathlib;sympy 1.14.0 / numpy 2.4.6 / scipy 1.17.1;**无 Singular**。

## Tier A — 完整 5/5(生成器机械写出 .lean + 独立验证)

| 模块 | 内容 | 生成器 | 验证 |
|---|---|---|---|
| `ScrHopf4D` | M4droop 特征多项式接地 + χ₄=err0+droop(~1038 项 ring) | `gen_chi4_lean`+`generate_scrhopf4d` | `verify_chi4_numeric` |
| `ScrHopfAnchor` | fold 处 χ₄=droop;轴无关 IVT 边界存在 + 真伪 | `generate_scrhopf_anchor` | `verify_anchor`,`verify_anchor_chain` |
| `ScrHopfCubic` | χ₄(gθ) 三次;L₃>0 把强网端从假设变定理(渐近+IVT) | `gen_cubic_coeffs`+`generate_scrhopf_cubic` | `verify_cubic_anchor` |
| `ScrHopfNumeric` | 具体 4D pHopf(deg-16,621 位)IVT 根,**SCR≈0.0378** | `generate_scrhopf_numeric` | `verify_hopf_elim` |
| `ScrHopf3DNumeric` | 3D keep-i_d(Schur)p3(deg-12,464 位),**SCR≈0.0377** | `generate_scrhopf3d_numeric` | `verify_hopf_elim_3d` |

## Tier B — 闸门通过 + 独立数值/CAS 交叉验证(Lean 手写或 CAS 辅助,无"机械写 .lean"那步)

| 模块 | 内容 | 验证脚本 |
|---|---|---|
| `FoldHopf` | 2D 无孤立 Hopf;3D χ 因式;fold⟺gθ=0;Ψ̃ spurious | `verify_fold_hopf`,`verify_fold_hopf_b` |
| `FoldHopfDecouple` | err=0 ⟹ J03=J13=0 ⟹ 2D=3D=4D 块上三角 fold-only | `verify_decouple` |
| `ScrHopf` | M3droop 特征多项式 + χ₃ droop 分解 | `verify_scr_hopf` |
| `ScrHopfExist` | `hopf_deg4` 真伪判据;χ₃ 仿射 ⟹ 根在 fold 外 | `verify_scr_params`,`verify_nonfixedpoint`,`verify_chi_locus` |
| `ScrAxis` | SCR(Lg) 严格递减;Hopf 抬到物理 SCR 轴 | `verify_scr_axis` |
| `LFilterHopf` / `LFilterT3` | L-filter GFL 三态:cubic Hopf 面;T3 Σ_iq−Σ_id 因式 | `validate_lfilter`,`T3_crosscheck` |

## Tier C — 闸门通过、proved,无专属数值验证(基础/纯代数,闸门即验证)

`Model`(Lemma 0 Power Lock)、`TheoremA`(unanchored Jacobian 零特征值)、`TheoremB`(慢模 −b=−D/2H)、`TheoremC`(振荡起始 λ²+bλ+βKs)、`AsymptoticB`(O(b²) 界)、`Calculus`(IFT/导数补全)、`HopfFold`(deg-2/3 Routh + Hopf 起始)、`LiteralModel`/`LiteralJacobian`(literal 模型 InnerField + C¹)、`LossOfSync`、`SyncEquilibrium`(鞍结)、`SlowModeScalar`(特征值⟺标量零点)、`ScrHopfDim`(三次 IVT + 维度阈值 punchline + 端到端 4D)、`GFL`(根模块)、`Audit`(闸门本体)。

这些是 pH-DAE / GFL 慢模 / L-filter 的基础结果与参数化组装,都是公理干净的机器证明;纯代数恒等式/Lean 结构证明,**闸门本身就是验证**,不需要(也没有)numpy 交叉验证那一步。

## Tier D — 不通过,未收(独立旧工程)

`formalization/archive/{DeepDifficulties,DifficultiesVerified,PowerSystem}.lean` 与 `archive/phdae/{Dynamics,PHDAE,PHEnergyBalance,lakefile}.lean`:独立的、被取代的早期工程(自带 lakefile),**不在活跃 lake 工程的闸门里**,故不通过、不收。

## 目录结构

```
03/
├── README.md          ← 本审计
├── lean/      (27)     ← 26 个活跃 GFL 模块 + GFL.lean 根
├── generators/ (25)    ← CAS 模型/推导 + 写 Lean 的生成器
└── verify/     (16)    ← 独立 numpy/scipy 验证 + validator
```

## 复现 / 验证

```bash
# 公理闸门(权威):
cd ../formalization/gfl && bash scripts/check_axioms.sh    # 146/146,无 sorryAx
# Tier A 端到端(以 4D 为例):
python3 generators/gen_chi4_lean.py && python3 generators/generate_scrhopf4d.py   # CAS→Lean
python3 verify/verify_hopf_elim.py                                                # 独立重跑消元+特征值
```

## 明确 OPEN(不冒充)

(1) **4D lossy 具体 SCR(≈0.0347)**:符号消元在本环境(无 Singular)全部 OOM/超时 —— Singular 领域,Lean 侧只差消元产出系数那一步。
(2) **根唯一性**:Mathlib 无 Sturm;只有局部唯一可做,未做。
(3) **无理根处 a₁,a₃>0**(严格真伪):平衡是 Lg 的代数函数,norm_num 够不着代数数符号 —— 靠数值交叉验证背书。
(4) **T2 理想成员证书**:lossy 尺度爆炸;pHopf↔系统 Hopf 链接靠构造+数值,不在 Lean 内。
