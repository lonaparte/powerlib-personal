# 02 — 通过标准化验证流程的形式化证明

本目录只收一类内容:**完全遵循同一套验证流程**的形式化证明。这套流程是从本项目 R1
"造模型"事故中长出来的(见 `../formalization/risk_mechanisms/R1_RETRACTED.md`),核心是
**先核对对象、再谈证明**,绝不让数值结果冒充形式证明。

不符合的内容(数学正确但卡在第 1 步对象闸门——经典摆模型,非仓库提交的 GFL)**未收入此处**,
仍留在 `../formalization/risk_mechanisms/`,并在那里明确标注为"经典对照"。

## 标准化验证流程(6 步)

1. **对象闸门**:验证"被分析的对象就是真实模型",而非凭记忆/方便编造。
   判据:`‖f(x*)‖≈0`(真平衡)+ Jacobian 与权威实现逐元对照 + 谱对照。
2. **命题参数化**:命题写成参数向量的关系(dL 的 `∀` 量化);具体数值只作事后核对,不进 Problem 块。
3. **结构提升**(当原对象 QE 不可处理时):抬到结构相同、但低阶可判定的数学层
   (如 10 阶 Hurwitz → degree-4 Liénard–Chipart;极限环 Floquet → Hopf 法形幅值方程)。
4. **KeYmaera X 证明**:每条命题一个 ArchiveEntry(Problem + Tactic),KeYmaera X 报 `PROVED`。
5. **数值交叉验证**(CLAUDE.md 要求 ≥3 组参数):把证完的结构回到真模型对数。
6. **诚实分层记录**:每条结论钉到 dL 已证 / interval / 数值 / open 之一,open 附精确阻塞原因。

## 收录内容与逐步对照

### `risk_mechanisms/` — R2real(Tier A:锚定**仓库提交的** §12 模型 `sweep.py`)

`kyx/R2real_fold.kyx`(5 条,全 proved):真模型的鞍结失平衡(电压崩溃)边界 `disc=0`,系数全是
`sweep.py` 平衡的真系数。

| 步 | 落实 |
|---|---|
| 1 对象闸门 | `numerical/R1_real_model_test.py`、`R2R3_model_audit.py`:从 `sweep.py` 真平衡导系数;确认 `M=K2` 可追溯、`\|M\|=Vg` 非真 fold(d 轴 Cterm≈300 不可略) |
| 2 参数化 | `∀ a2 a1 a0 …` / `∀ wn Vg Rg Lg Cf idr`,无固定数值入命题 |
| 3 结构提升 | 平衡数 → vcd 二次判别式(标量,QE 可判定) |
| 4 证明 | KeYmaera X 5/5 PROVED |
| 5 数值核对 | `numerical/R2real_validate.py`:disc 符号 ⟺ 真平衡数,3 组参数,残差~1e-11,且与 `sweep.py` 的 `pv()` 崩溃边界逐点吻合 |
| 6 分层 | README 标"真模型 §12,fold 在 SCR*≈0.370" |

### `freq_boundary/` — F-H / F-fold(Tier B:锚定**任务给定的** converter-frame RHS)

> Tier B 说明:任务模型 = `run_sde_schafer.full_dynamics_ad`,**该文件不在仓库**;其谱与 `sweep.py`
> 不同(Hopf 0.950 vs 0.905)。对象闸门已做(`fh_gate.py`,平衡残差~1e-10、谱核对),但对象是
> **任务给定的良定义模型**,非仓库提交模型——已如实标明。证书本身是 Tier-A 级的结构提升 + QE 证明。

- `kyx/fh_hopf_signature.kyx`(3):F-H 的 Hopf 签名机制(degree-4 Liénard–Chipart:`Δ₃=0 ⟹ 纯虚对`,
  与模型 Δ₉=0 同构)。闸门 `fh_gate.py`+`fh_hurwitz.py`(真模型 Σ_H 签名)、负结果 `fh_reduce.py`
  (不可低阶约化)、子空间显式 `fh_sigmaH_pll.py`;数值核对:5 组随机 deg-4 多项式 + 真模型 Σ_H。
- `kyx/ffold_cyclefold_normalform.kyx`(5):F-fold 环折叠 = Hopf 法形幅值方程鞍结(与 R2real 同型)。
  闸门 `ffold_normalform.py`(法形成立 + Bautin Kp*≈0.43);数值核对 `ffold_l2_branch.py`(l₂>0 非退化)
  + `ffold_locate.py`(折叠定位 μ∈[4.24,8.53],与法形预测 μ_fold=5.86 自洽)。F1 证据 `ffold_cycle.py`
  (Floquet \|μ\|=0.881<1)+ `ffold_l1_anchor.py`(l₁<0)。
- `kyx/ffold_f3_drift.kyx`(2):F3 角漂移子块(`\|M\|>Vg ⟹ 无界漂移`),R2/Σ₂ 同型。

## 未收录(不符合,卡在第 1 步)

留在 `../formalization/risk_mechanisms/kyx/`,标注为经典对照:
- `R2_fold.kyx`、`R2_sigma2_symbolic.kyx` — 经典单摆 fold `Φ=M²−Vg²`(非 §12 真 fold)。
- `R3a_energy_barrier.kyx`、`R3_basin.kyx`、`R3note_decoupling.kyx` — 经典摆动方程(不在任何提交模型里)。

这 5 个证书数学上都 proved,但**对象是教科书单摆,不是仓库 GFL**——故不计入"遵循流程"的成果。

## 复现

```
# 证明(每个 .kyx)
cd 02 && java -Xss20M -jar <keymaerax.jar> -launch -prove risk_mechanisms/kyx/R2real_fold.kyx -tool z3
cd 02 && java -Xss20M -jar <keymaerax.jar> -launch -prove freq_boundary/kyx/fh_hopf_signature.kyx -tool z3
# 数值交叉验证
cd 02/risk_mechanisms/numerical && python3 R2real_validate.py
cd 02/freq_boundary && python3 ffold_normalform.py && python3 ffold_locate.py
```

合计 **15 条 KeYmaera X proved**(R2real 5 + F-H 3 + F-fold 7),全部通过 6 步流程。

## 审计范围(诚实说明)

本次审计**只覆盖本轮 session 产出/审查的证明**(risk_mechanisms + freq_boundary,共 9 个 .kyx)。
其中符合流程的 4 个(15 条)收入此处,不符合的 5 个经典摆证书留在原处。

**未审计**:仓库还有 **82 个预存 .kyx**(`formalization/archive/phdae/` 65、`formalization/freq_mode/kyx/`
16、`formalization/numerical/formal_bridge/` 1),它们早于本轮 session、不是在本流程下产出的,**本次
未逐条对照 6 步流程**。若需把它们也纳入同一审计(尤其逐个核对对象闸门),那是另一项单独工作。
