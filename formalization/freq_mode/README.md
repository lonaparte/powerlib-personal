# 已迁移 → /02/freq_mode/

本目录全部内容(16 个 .kyx / 34 条 KeYmaera X 证明 + verify_freq_mode.py + FREQ_MODE.md
+ STATUS.md + results)经全分支 6 步流程审计**全部通过**后,移至仓库根 **`/02/freq_mode/`**:

- 对象闸门:`verify_freq_mode.py` 24/24(18 精确符号,对 Conventions §13 单一真源)
- 参数化:STATUS.md 明示全符号、无定值(1.5 为 §13 模型结构常数)
- 本轮重证:16 文件 / 34 entries 全 `PROVED`(KeYmaera X 5.1.2 + 自带 z3)
- 独立交叉:`prove_freq_mode_z3.py` 12/12 参数化义务
- 分层记录:STATUS.md 四层,sympy 层与 dL 层边界逐条明示

审计记录见 `/02/README.md`。
