# 03 — SCR-Hopf 形式化:流水线一致的证明归档

本目录是一份**精选归档**:把 GFL-VSC 弱网 SCR-Hopf 工作中**遵循同一条五步流水线**的证明集中到一处,便于审阅与复现。

> **这些是副本**。可编译的权威源在 `formalization/gfl/`(一个 Lean 4 + Mathlib 的 lake 工程)。
> 本目录里的 `.lean` **不单独编译**——它们依赖该 lake 工程里的引擎模块(`FoldHopf`、`ScrHopfExist`、`HopfFold` 等)。
> 公理闸门(第 ④ 步)在 `formalization/gfl/` 上跑:`scripts/check_axioms.sh`,当前 **146/146** 通过,公理恰为 `[propext, Classical.choice, Quot.sound]`,无 `sorryAx`、无 `native_decide`。

## 五步流水线

1. **模型层(sympy)** —— 4D P-only GFL 的显式方程 → 平衡(F₀,F₁ 对 i_d,i_q 线性求解)→ Jacobian → 特征多项式系数 a₁…a₄ → Routh–Hurwitz Hopf 量 χₙ。单变量化用 Weierstrass `t=tan(θ_e/2)` + 结式消元。
2. **生成器** —— `gen_*.py` / `generate_*.py` 把 CAS 产物(多项式字面量/系数)**机械转**成 Lean 源,杜绝手抄错。
3. **Lean 4 机器证明** —— `ring`(大恒等式)、`norm_num`(整数端点符号)、`intermediate_value_Ioo`(IVT)、re/im 分解 + `linear_combination`(纯虚根)、`det_succ_row_zero`+`det_fin_three`(4×4 行列式接地)、多项式渐近(`tendsto_atTop_of_leadingCoeff_nonneg`)、`gcongr`/`positivity`(单调/正性)。
4. **公理闸门** —— `#print axioms` 必须恰为标准三公理,无 `sorryAx`。
5. **独立数值验证** —— `verify_*.py` 用**独立于生成路径的 numpy/scipy**(`numpy.poly` 特征多项式、`fsolve` 平衡、特征值穿越)对账到 1e-6~1e-13,确认 Lean 证的代数对象就是物理 Hopf。

环境:Lean 4 `v4.31.0-rc1` + Mathlib(同 rev);sympy 1.14.0 / numpy 2.4.6 / scipy 1.17.1。**无 Singular**(4D lossy 精确消元因此卡住——见下方 OPEN)。

## 收录文件 × 流程符合度

| Lean(`lean/`) | 证明内容 | ① 模型 | ② 生成器 | ③ Lean | ④ 闸门 | ⑤ 验证 | 符合 |
|---|---|---|---|---|---|---|---|
| `ScrHopf4D` | M4droop 特征多项式接地(4×4 det)+ χ₄ = err0 + droop 分解(~1038 项 `ring`) | `gen_chi4_lean.py` | `generate_scrhopf4d.py` | ✓ | ✓ | `verify_chi4_numeric.py` | **5/5** |
| `ScrHopfAnchor` | fold 处 χ₄=droop;轴无关 IVT 引擎:变号 ⟹ 边界在 fold 外存在 + 真伪 | gen_chi4(共用) | `generate_scrhopf_anchor.py` | ✓ | ✓ | `verify_anchor.py`,`verify_anchor_chain.py` | **5/5** |
| `ScrHopfCubic` | χ₄(gθ) 三次多项式;首项 L₃>0 把强网端从假设变成定理(渐近 + IVT) | `gen_cubic_coeffs.py` | `generate_scrhopf_cubic.py` | ✓ | ✓ | `verify_cubic_anchor.py` | **5/5** |
| `ScrHopfNumeric` | 具体 4D pHopf(deg-16,621 位)`norm_num`+IVT 根 ∈ (0.121444,0.121445),**SCR≈0.0378** | 消元(verify 内) | `generate_scrhopf_numeric.py` | ✓ | ✓ | `verify_hopf_elim.py` | **5/5** |
| `ScrHopf3DNumeric` | 3D keep-i_d(Schur)p3(deg-12,464 位)根 ∈ (0.121779,0.121780),**SCR≈0.0377** | 消元(verify 内) | `generate_scrhopf3d_numeric.py` | ✓ | ✓ | `verify_hopf_elim_3d.py` | **5/5** |
| `ScrAxis` | SCR(Lg)=Vn²/(Sn·Lg·wn·zfac) 严格递减;Hopf 抬到物理 SCR 轴,SCR*>0 真 Hopf | N/A(公式定义) | N/A(手写) | ✓ | ✓ | `verify_scr_axis.py` | 3/5 |
| `ScrHopfDim` | 三次 IVT 引擎 + 3D 参数化 SCR-Hopf + **维度阈值 punchline**(2D 无 / 3D,4D 有)+ 端到端 4D | N/A(组装) | N/A(手写) | ✓ | ✓ | N/A(抽象见证) | 2/5 |

**严格 5/5**(完整 CAS模型→生成器→Lean→闸门→独立验证):前五个。
**参数化核心**(手写 Lean,无 CAS/生成器——因为是抽象参数化/引擎组装,无可生成的字面量,但是机理主干、闸门通过):`ScrAxis`、`ScrHopfDim`。

## 复现

```bash
# 模型 + 生成(以 4D 分解为例):产出 formalization/gfl/GFL/ScrHopf4D.lean
python3 generators/gen_chi4_lean.py        # CAS: M4droop charpoly, 写 /tmp/chi4_lean.txt
python3 generators/generate_scrhopf4d.py   # 转成 Lean 源

# 独立数值验证(不依赖生成路径)
python3 verify/verify_chi4_numeric.py      # numpy 对账,max err ~1e-14
python3 verify/verify_hopf_elim.py         # 重跑消元 + 特征值交叉验证 4D Hopf 根
python3 verify/verify_hopf_elim_3d.py      # 同上,3D keep-i_d

# 公理闸门(在 lake 工程上)
cd ../formalization/gfl && bash scripts/check_axioms.sh   # 期望 146/146,无 sorryAx
```

## 已证结论(一句话)

- **机理(参数化,符号参数,无嵌入数值)**:2D 无孤立 Hopf;χ₃/χ₄ 的 droop 分解(误差注入项把 Hopf 与 fold 分离);`hopf_deg{3,4}` 真伪判据(ω²=a₃/a₁>0 排除 spurious);anchor 把强网端从假设降到结构条件 L₃>0;SCR↔Lg 反单调;**维度阈值:2D 不可能、3D/4D 可能**;端到端 4D:`L₃>0 ∧ χ₄(0)<0 ∧ a₁,a₃>0 ⟹ 真 Hopf 在 SCR>0`。
- **具体数值(lossless,GFL 有理参数代理)**:4D `SCR≈0.0378`、3D keep-i_d `SCR≈0.0377`,均 1e-6 紧锚、norm_num+IVT 机器证、独立特征值交叉验证为真 Hopf。

## 明确 OPEN(不冒充)

1. **4D lossy 的具体 SCR(≈0.0347)**:符号消元(直接/eval-interp/Cramer)在本环境全部 OOM/超时——sympy 极限,需 **Singular** oracle 系数。Lean 侧(嵌系数 + norm_num + IVT)与 lossless 同构,只差消元产出那一步。
2. **根唯一性**:Mathlib 无 Sturm 定理,Descartes 给 11 个符号变号(无用);仅局部唯一(中值不等式)可做,未做。
3. **无理根处 a₁,a₃>0**(严格真伪性):平衡是 Lg 的代数函数,`norm_num` 够不着代数数符号——原理墙,靠数值交叉验证背书。
4. **T2 理想成员证书**(pHopf↔χ₄ 的 `ring` 恒等):lossy 尺度爆炸;链接靠构造 + 数值验证,不在 Lean 内。
