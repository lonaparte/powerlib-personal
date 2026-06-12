# archive/phdae — 留档说明(2026-06 全分支审计后)

通过 6 步审计流程的 **27 个 Summary 注册证书已迁至 `/02/phdae/kyx/`**(连同 .kyp 与
`validate_boundary.py`)。审计记录与数值交叉验证见 `/02/phdae/README.md`。

## 本目录现存内容及其状态

- **4 个重 QE 超时的注册证书**(`asymptotic_d2_small`、`asymptotic_weak_coupling`、
  `conjecture_neg_d2_lyapunov`、`theorem_3machine`):历史 .kyp(2026-05)在,本轮本环境
  (4 核)300s+600s 双超时(SIGTERM)。**超时 ≠ 证伪**;更强机器复验通过即可补入 02。
- **2 个未证 conjecture**(Problem-only,按约定):`conjecture_instability_boundary`、
  `conjecture_parametric_asymptotic`。
- **~26 个未注册迭代草稿**:被后续版本取代或未收入 Summary 的探索版本(本轮多数也重证
  通过,4 个超时 FAIL:`exact_necessary`、`impossibility_parametric`、`gap_parametric`、
  `theorem_levelC_polynomial`)。archive 本意即保全历史。
- **4 个 Lean 工件**(PHDAE.lean 等):本环境无 Lean 工具链,无法复验,留档待验。
- `schur_preserve.py`:研究探索脚本(Schur 补保结构性的否定实例),非验证 harness。
