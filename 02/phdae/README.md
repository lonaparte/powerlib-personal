# 02/phdae — pH-DAE / SMIB / 两机·三机线的注册证明(通过 6 步流程审计)

> 来源:`formalization/archive/phdae/`(2026-05 早期 session 产出)。本目录收其中
> **通过全分支审计**的部分:Summary.md 注册 ∩ 机械重证通过 ∩ 对象闸门核验。
> 迭代草稿(未注册)、未证 conjecture、Lean 工件**留在原 archive**(见"未收录")。

## 审计证据(6 步逐项)

1. **对象闸门**:
   - 8 个含内联 ODE 的文件:与 Conventions §2(sin/cos 编码)、§3(两机系统)**逐项一致**
     (脚本化结构核对,零偏差,无 R1 式"冻结项")。
   - **SMIB 模型缺口已修复**:smib_* 证书的单机模型原先不在 Conventions(违反"新约定先进
     Conventions");审计时从 8 个相互一致的 smib 证书中提取,补登为 **Conventions §14**。
   - **深度抽查(协议第 4 条,Lie 导数手工核验)**:主线 `theorem_ph_bridge_parametric.kyx`
     的两条 V̇ 多项式(6·V̇|_{c=1}、30·V̇|_{c=4/5})用 sympy 独立复算,**逐项恒等(差=0)**。
2. **参数化 / 声明定值**:12 个 Problem 含非平凡数字的文件逐个核:全部是**声明在标题/注释里的
   定点反例或定值证书**(如 gap@d=19/20、impossibility@D2=−3/10、3machine 带诚实范围注
   "只证 (0,19/100) 非全 (0,1/5)")——符合协议"定值须声明"。其余全符号参数。
3. **KeYmaera X 重证**:全部条目本轮在 KeYmaera X 5.1.2(自带 z3)重证 `PROVED`
   (见仓库提交信息中的统计;`*.kyp` 缓存随文件保留)。
4. **数值交叉验证**:`numerical/validate_boundary.py` ——**独立实现**(np.sin 真非线性两机系统,
   非 s,c 编码)模拟找分界面,交叉验证 H_crit≈4K+8D√K 边界。
5. **结构提升**:V̇ 恒等式/Sylvester 子式/判别式等代数化是该线的固有方法(dL 证代数命题,
   Lie 导数 sympy/手工导出后由本审计抽查)。
6. **分层记录**:`formalization/Summary.md` 为注册索引;此处为审计后的"注册且通过"子集。

## 收录(31 个 .kyx)

Summary 注册的 33 个中:30 个常规证明 + 1 个**已证前猜想**(`conjecture_neg_d2_lyapunov.kyx`,
按 CLAUDE.md 约定"证出后加 Tactic、文件名不变")。各文件含义见 `formalization/Summary.md` 索引。

## 未收录(留在 formalization/archive/phdae/)

- **30 个未注册文件**:迭代草稿/被后续版本取代(archive 本意即全历史)。多数本轮也重证通过,
  但未经 Summary 注册 = 不属于项目声明的成果集,按流程第 6 步不收。
- **2 个未证 conjecture**(Problem-only):`conjecture_instability_boundary.kyx`、
  `conjecture_parametric_asymptotic.kyx` ——猜想不是证明。
- **4 个 Lean 工件**(PHDAE.lean 等):本环境无 Lean 工具链,**无法复验**,不能确认第 4 步。
- `schur_preserve.py`:研究探索脚本(否定实例打印),非验证 harness。

## 复现

```
java -Xss20M -jar <keymaerax.jar> -launch -prove kyx/<file>.kyx -tool z3
python3 numerical/validate_boundary.py     # 独立数值边界验证(慢)
```
