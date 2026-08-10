# 对象模型与推导(2026-08-10 定版)

本文件是 04 战役对象模型的**权威陈述**与其**推导过程**。README 的"对象模型"
段是索引,细节以本文件为准。所有断言分两类标注:**[证]** = 符号/代数证明,
**[测]** = 数值见证(给出日志与量级)。

约定见工作区 `conventions.md` §D:**IN-positive**(电流流入变流器为正、$Q$ 吸
收为正)。复功率一律从 $\bar S=\bar V\bar I^*$ 起手,不背 $P,Q$ 分量公式。

---

## 1. GFL —— 八态(默认工作模型)

### 1.1 方程

状态 $x=(\theta,\;x_p,\;V_{dc},\;\xi,\;i_d,\;\gamma_d,\;i_q,\;\gamma_q)$。

代数量(PLL 坐标系):

$$v_{gd}=V\cos\theta-X_g i_q,\qquad
v_{gq}=-V\sin\theta+X_g i_d,\qquad
|v_{pcc}|=\sqrt{v_{gd}^2+v_{gq}^2}$$

指令:

$$i_d^*=k_{pv}(1-V_{dc})+k_{iv}\xi,\qquad
i_q^*=\begin{cases}Q & \text{(A) 外生无功指令}\\[2pt]
Q+k_q\big(V_{ref}-|v_{pcc}|\big) & \text{(B) 无功/电压环}\end{cases}$$

微分方程:

$$
\begin{aligned}
\dot\theta &= k_p v_{gq}+k_i x_p\\
\dot x_p &= v_{gq}\\
\dot V_{dc} &= \frac{1}{C}\Big(P+\tfrac32\,\frac{v_{gd}i_d+v_{gq}i_q}{V_{dc}}\Big)\\
\dot\xi &= 1-V_{dc}\\
\dot i_d &= 2\zeta_c\omega_c\,(i_d^*-i_d)+\omega_c^2\gamma_d, &\dot\gamma_d &= i_d^*-i_d\\
\dot i_q &= 2\zeta_c\omega_c\,(i_q^*-i_q)+\omega_c^2\gamma_q, &\dot\gamma_q &= i_q^*-i_q
\end{aligned}
$$

**不含**:限流、PLL 饱和、直流源动态、开关谐波。

### 1.2 电流环两行的来历(不是唯象滞后)

$dq$ 轴电流动态在精确前馈 + 解耦下(用测得的 $\omega_1$ 抵消 $\pm\omega_1L_fi$,
用测得的 $v_g$ 抵消端电压)化为

$$L_f\dot i_d=k_{pc}(i_d^*-i_d)+k_{ic}\gamma_d-R_fi_d,\qquad \dot\gamma_d=i_d^*-i_d$$

闭环传函 $\dfrac{i_d}{i_d^*}(s)=\dfrac{k_{pc}s+k_{ic}}{L_fs^2+(k_{pc}+R_f)s+k_{ic}}$。
与 1.1 的二阶形式对照 **[证]**:

$$\boxed{\;\omega_c=\sqrt{k_{ic}/L_f},\qquad
\zeta_c=\frac{k_{pc}+R_f}{2\sqrt{k_{ic}L_f}},\qquad
H(s)=\frac{2\zeta_c\omega_c s+\omega_c^2}{s^2+2\zeta_c\omega_c s+\omega_c^2},\quad H(0)=1\;}$$

$H(0)=1$ 来自积分器,故稳态 $i=i^*$,**平衡点与四态完全一致**;$R_f$ 只并入
$\zeta_c$(把 $R_f$ 独立保留会让零点移到 $-k_{ic}/k_{pc}$,与本式的
$-\omega_c/2\zeta_c$ 差 $R_f/k_{pc}$ 阶,本战役取 $R_f=0$)。

**不许**把这两行当成"一阶滞后 $\dot i=\omega_c(i^*-i)$"再声称等价——一阶形式
没有积分器,零点结构不同,只能作探针(见 `scripts/gflinner.py` 的五态探针)。

### 1.3 平衡点与退化

平衡时 $i_d^*-i_d=0,\;i_q^*-i_q=0$,回代第五、七行得 $\gamma_d=\gamma_q=0$。
故四态平衡点**精确提升**:

$$x^{(8)}=\big(\theta^\star,\;x_p^\star,\;V_{dc}^\star,\;\xi^\star,\;i_d^*(V_{dc}^\star,\xi^\star),\;0,\;Q,\;0\big)$$

**[测]** 残差 $7.6\times10^{-13}$(`logs/qaxis.log`)。$\omega_c\to\infty$ 精确
回到四态 $(\theta,x_p,V_{dc},\xi)$、$i_q\equiv Q$。

G1 格 $P_0=1.4550001$(四态 Hopf $P_H=1.4551540$ 的 margin 0.10):

| 量 | 值 |
|---|---|
| $\theta$ | $-0.662616$ |
| $x_p$ | $0$ |
| $V_{dc}$ | $1$ |
| $\xi$ | $-0.024607$ |
| $i_d$ | $-1.230362$ |
| $i_q$ | $0$ |
| $v_{gq}$ | $0$(PLL 锁定) |
| $\|v_{pcc}\|$ | $0.788386$ |
| 特征值 | $-0.1000\pm32.3988i$(临界,$\zeta=0.0031$);$-5.9886\pm41.2444i$ |

$i_d<0$ 是 IN-positive 下"向电网送有功"的正确符号。

---

## 2. 块三角定理(为什么冻结 $i_q$ 对自治侧零代价)

设 $x=(x_d,x_q)$,$x_d=(\theta,x_p,V_{dc},\xi,i_d,\gamma_d)$,$x_q=(i_q,\gamma_q)$。

**情形 (A)**($i_q^*$ 外生):q 两行只含 $(i_q,\gamma_q)$ 与外生量,故

$$\dot x_d=f_d(x_d,x_q),\qquad \dot x_q=f_q(x_q;u)
\;\Longrightarrow\;
J=\begin{pmatrix}A_{dd}&A_{dq}\\[2pt] 0&A_{qq}\end{pmatrix}$$

**[证]** $\partial(\text{q 行})/\partial(\text{其余六态})\equiv 0$(符号判定),
而 $\partial(\text{d 行})/\partial i_q\neq0$ 仅在第 3 行(直流母线功率),即
$A_{dq}=(g,\,0)$($\gamma_q$ 不进 $f_d$)。**单向驱动:q 块驱动 d 块,反之不然。**

由此逐条:

1. **谱分裂**:$\det(sI-J)=\det(sI-A_{dd})\det(sI-A_{qq})$。
2. **右特征向量**:$A_{dd}v_d=\lambda v_d\Rightarrow J(v_d,0)^T=\lambda(v_d,0)^T$。
   临界右特征向量的 **q 分量恒为零**。
3. **左特征向量**:$p^HJ=\lambda p^H$ 给
   $p_d^HA_{dd}=\lambda p_d^H$ 与
   $$p_q^H=p_d^HA_{dq}\,(\lambda I-A_{qq})^{-1}\neq0\ \text{(一般)}$$
4. **张量的 q 行恒零**:$f_q$ 对状态是**线性**的,故
   $B(\cdot,\cdot)$、$C(\cdot,\cdot,\cdot)$ 的 q 行 $\equiv0$。
5. **同调解不越界**:$B(q,q)$ 只有 d 分量;解
   $(2i\omega_0I-J)h_{20}=B(q,q)$ 的 q 行给 $(2i\omega_0I-A_{qq})h_{20,q}=0
   \Rightarrow h_{20,q}=0$(只要 $2i\omega_0\notin\mathrm{spec}\,A_{qq}$),
   d 行退化为六态方程。$h_{11}=-A^{-1}B(q,\bar q)$ 同理。
6. **投影一致**:被投影的向量 q 分量全零 ⇒ $\langle p,\cdot\rangle=
   \langle p_d,\cdot_d\rangle$;归一化 $\langle p,q\rangle=\langle p_d,q_d\rangle$
   也一致。

$$\therefore\quad
c_1=\tfrac12\Big[\langle p,C(q,q,\bar q)\rangle-2\langle p,B(q,h_{11})\rangle
+\langle p,B(\bar q,h_{20})\rangle\Big]
\;\text{与六态恒等},\quad \alpha,\omega_0\ \text{同理}\qquad\blacksquare$$

**[测]** $x=\omega_c/\omega_0=10/30/100$ 时 $\alpha,\omega_0,\mathrm{Re}\,c_1$
的 reldiff **$0.00\mathrm{e}{+}00$**;$x=300$ 为 $4.6\mathrm{e}{-}10$ /
$8.7\mathrm{e}{-}12$(浮点极限)。对照:V 通道(无 q 分量)六态与八态阈值差
$3.3\mathrm{e}{-}16$。日志 `logs/qaxis.log`。

**结论**:冻结 $i_q$ 对 Hopf 侧(α、ω₀、c₁)**零代价,是定理不是近似**。动 α
的是 **d 轴**电流环($\delta\alpha/\alpha\approx1100/x$,`logs/gflinner.log`),
q 轴电流环严格不动它。

**情形 (B)**(电压环):$i_q^*$ 含 $|v_{pcc}|$,而 $|v_{pcc}|$ 依赖 $\theta,i_d,i_q$
⇒ $\partial(\text{q 行})/\partial\theta\neq0$、$\partial(\text{q 行})/\partial i_d\neq0$
**[证]**,块三角消失,以上六条全部失效,**八态强制**。

---

## 3. q 轴驱动的传递:两个 $H$ 取在不同频率

q 块矩阵与驱动向量:

$$A_{qq}=\begin{pmatrix}-2\zeta_c\omega_c&\omega_c^2\\-1&0\end{pmatrix},\qquad
f_{u,q}=\begin{pmatrix}2\zeta_c\omega_c\\1\end{pmatrix}$$

**状态响应** **[证]**:解 $(i\omega_pI-J)h=f_u$,q 行给
$h_q=(i\omega_pI-A_{qq})^{-1}f_{u,q}$,其 $i_q$ 分量 $=H(i\omega_p)$;d 行给

$$(i\omega_pI-A_{dd})h_d=A_{dq}h_q=g\,H(i\omega_p)
\;\Longrightarrow\;
h_d=H(i\omega_p)\,h_d^{(6)}$$

即**六态 + 驱动前置 $H(s)$ ≡ 八态**(状态轨迹意义上精确)。

**模态耦合** **[证]**:

$$\langle p,f_u\rangle=p_q^Hf_{u,q}
=p_d^HA_{dq}(\lambda I-A_{qq})^{-1}f_{u,q}
=\langle p_d,g\rangle\,H(\lambda)$$

$H$ 取在**模态频率** $\lambda=-\alpha+i\omega_0$,而状态响应里 $H$ 取在**驱动频率**
$i\omega_p$。**两处取值点不同**,所以在册 Q 通道阈值的重标不是简单的
$1/|H(i\omega_p)|$。

---

## 4. 乘性驱动:扩展张量

### 4.1 问题

侵蚀机器把驱动当**加性**:$f(x,Q_0+u)\approx f(x,Q_0)+f_uu$,于是丢掉
$f_{ux},f_{uu},f_{uxx},\dots$。**[测]** $\varepsilon_c(8)/\varepsilon_c(6)$ 在
$\omega_c\to\infty$ **不趋于 1**,停在 $0.98350$($r=0.60$)、$0.99484$($r=0.90$)
——无穷带宽下的残差不可能是带宽效应。

### 4.2 推导

把驱动 $u$ 当作一个**无动力学的附加坐标**,$X=(x,u)$,只对 $f$ 的 $n$ 行求导。
定义扩展形式(下标遍历 states ⊕ u):

$$\tilde B(Y,Z)_i=\sum_{j,k}\frac{\partial^2f_i}{\partial X_j\partial X_k}Y_jZ_k,
\qquad
\tilde C(Y,Z,W)_i=\sum_{j,k,l}\frac{\partial^3f_i}{\partial X_j\partial X_k\partial X_l}Y_jZ_kW_l$$

驱动坐标对自身的"响应"是 1,临界模态在驱动坐标上无分量,故

$$\tilde q=(q,\,0),\qquad \tilde H=(H,\,1),\qquad H=(i\omega_pI-A)^{-1}f_u$$

resolvent 仍在 $n$ 维解(附加坐标无动力学,不进解算),中间量补零后再收缩:

$$g_\pm=\big(i(\omega_0\pm\omega_p)I-A\big)^{-1}\tilde B\big(\tilde q,\;\tilde H\ \text{或}\ \overline{\tilde H}\big),
\qquad d_0=-A^{-1}\tilde B(\tilde H,\overline{\tilde H})$$

$$\boxed{\;c_x=\big\langle p,\tilde C(\tilde q,\tilde H,\overline{\tilde H})\big\rangle
+\big\langle p,\tilde B(\tilde H,(g_-,0))\big\rangle
+\big\langle p,\tilde B(\overline{\tilde H},(g_+,0))\big\rangle
+\big\langle p,\tilde B(\tilde q,(d_0,0))\big\rangle\;}$$

把所有含驱动下标的张量元置零即退化回旧的加性 `cx_hand`。

### 4.3 判据与见证

**乘性 ⇔ 驱动参数在向量场里乘状态 ⇔ $\partial^2f/\partial x\,\partial u\neq0$。**
GFL:$V$ 乘 $\sin\theta,\cos\theta$;$Q$ 经 $v_{gq}Q$ 与 $v_{gd}$ 乘 $i_d$;
$P$ 只进直流母线的加性项。

**[测]**(`logs/qaxis3.log`,对照检验通过):

| 通道 | $c_x$ 加性 | $c_x$ 乘性 | 相对变化 |
|---|---|---|---|
| V | $+1.4902899\mathrm{e}{+}07$ | $+1.4968970\mathrm{e}{+}07$ | $+0.443\%$ |
| P | $+2.5936518\mathrm{e}{+}06$ | $+2.5936518\mathrm{e}{+}06$ | **$0.000\mathrm{e}{+}00$**(严格) |
| Q | $+2.2097093\mathrm{e}{+}06$ | $+2.2530540\mathrm{e}{+}06$ | $+1.962\%$ |

加性版复现旧 `cx_hand` 到 $5\mathrm{e}{-}16$。判决性检验:用扩展张量重算六态
$c_x$ 与八态比值,$x=100$ 时 $0.99991$、$x=1000$ 时 $1.00000$(加性版停在
$0.98350$)——**机理确认**(`logs/qaxis2.log`)。

回代在册 V 通道三阶预测(`logs/qaxis3.log`):

| 格 | margin | 实测 | 三阶(加性) | 三阶(乘性) |
|---|---|---|---|---|
| G1 r=0.9 | 0.05 | 8.433762e-05 | $+2.39\%$ | $+2.26\%$ |
| | 0.10 | 1.186533e-04 | $+3.56\%$ | $+3.43\%$ |
| | 0.15 | 1.446188e-04 | $+4.54\%$ | $+4.40\%$ |
| | 0.20 | 1.662438e-04 | $+5.40\%$ | $+5.26\%$ |
| idx17 r=0.92 | 0.08 | 7.099020e-03 | $+0.46\%$ | $-0.30\%$ |

**乘性项量级 0.1–0.8pp,是一致平移,不解释随 α 增长的那部分残差**(仍属五阶)。

---

## 5. 无功/电压环:一阶系数是公式参数

$i_q^*=Q+k_q\big(V_{ref}-|v_{pcc}|\big)$。取 $V_{ref}=|v_{pcc}|_0$ 使 $i_q^*|_0=Q$,
**平衡点集合不变**,只有 $J$ 变(等价于 `gfminner` 用过的保平衡点设计)。

**符号** **[证]**:$\dfrac{\partial|v_{pcc}|}{\partial i_q}=-\dfrac{X_gv_{gd}}{|v_{pcc}|}$,
在工作点 $=-0.500<0$(升 $i_q$ 压端电压)。回路增益
$\delta i_q^*=-k_q\dfrac{\partial|v|}{\partial i_q}\delta i_q$,负反馈要求
$k_q\dfrac{\partial|v|}{\partial i_q}>0$,即 **$k_q<0$ 才是调压向**。

> **已作废**:本轮第一次扫的是 $k_q>0$ 支并称其"regulating",符号取反,那是
> 正反馈。相应的 $k_q=+0.1$ 即失稳的结论不代表真实 AVR。

**一阶摄动**(单特征值,$\langle p,q\rangle=1$)**[证]**:

$$\boxed{\;\frac{d\lambda}{dk_q}=\Big\langle p,\;\frac{\partial A}{\partial k_q}\,q\Big\rangle\;}
\qquad\Longrightarrow\qquad
\frac{d\lambda}{dk_q}=55.83-29.09\,i$$

即 $d\alpha/dk_q=-55.83$、$d\omega_0/dk_q=-29.09$。

**[测]**(`logs/qaxis3.log`、`logs/qaxis4.log`):

- 反调向($k_q>0$)失稳增益闭式 $k_q^{crit}=\alpha_0/|d\alpha/dk_q|=0.001902$,
  实测 $0.001921$,**比 1.010**。
- 正调向($k_q<0$)把被跟踪模态强阻尼($k_q=-0.1$ 时 $\alpha$ 由 $0.106$ 升到
  $5.83$,特征向量重叠 $0.9924$),但**电压环自带的新模态**($\omega\approx43.6$)
  成为最弱阻尼,在 $k_q=-0.1085$ 越界。
- 线性预测在 $|k_q|\le0.01$ 内与直扫差 $<5\%$;$|k_q|\gtrsim0.2$ 后重叠跟踪
  失效(分支跳变),该区不引用。

**含义**:GFL 开环 $\alpha=0.106$($\zeta=0.0031$)在 $k_q\sim10^{-3}$ 就被完全
改写——**α 什么都推得动,不能继承**。

---

## 6. GFM —— 四态(默认)与六态(精化)

### 6.1 四态最小 VSM

状态 $x=(\delta,\omega,P_f,Q_f)$:

$$E=E_{nom}-m_q(Q_f-Q_{ref}),\qquad
P_e=\frac{EV\sin\delta}{X_g},\qquad
Q_e=\frac{E^2-EV\cos\delta}{X_g}$$

$$\dot\delta=\omega,\quad
\dot\omega=\frac{P_{ref}-P_f-D\omega}{M},\quad
\dot P_f=\omega_c(P_e-P_f),\quad
\dot Q_f=\omega_c(Q_e-Q_f)$$

虚拟阻抗:$X_g\to X_g+X_v$(**[证]** $\omega_c\to\infty$ 精确回到本式)。

四格:A = M2/$X_g$0.5/90%,B = M3/0.5/90%,C = M2/0.3/75%,D = M3/0.3/90%;
M2 = $(M,D,m_q,\omega_c)=(0.1,0.2,0.05,2\pi\!\cdot\!10)$,
M3 = $(0.005,0.02,0.2,2\pi\!\cdot\!100)$;$V=1,Q_{ref}=0$。
$\omega_0$ = 2.7283 / 12.4160 / 4.5202 / 16.0073,$\zeta$ = 0.326 / 0.152 / 0.183 / 0.115。

### 6.2 GFM 的 q 轴本来就是动态的 **[证]**

$$i_q=\frac{V\cos\delta-E}{X_g}
\;\Longrightarrow\;
\frac{\partial i_q}{\partial\delta}=-\frac{V\sin\delta}{X_g}\neq0,\qquad
\frac{\partial i_q}{\partial Q_f}=\frac{m_q}{X_g}\neq0$$

$i_q$ 是**两个状态的函数,从来不是参数**。故 GFM 没有"冻结 $i_q$"这件事要拆,
q 轴扰动就是在册 Q($Q_{ref}$)通道。

### 6.3 六态(带电流环)

$$i_d^s=\frac{V\sin\delta}{X_g},\qquad i_q^s=\frac{V\cos\delta-E}{X_g},\qquad
P_e=E\,i_d,\qquad Q_e=-E\,i_q$$

$$\dot\delta=\omega,\quad \dot\omega=\frac{P_{ref}-P_f-D\omega}{M},\quad
\dot P_f=\omega_c(Ei_d-P_f),\quad \dot Q_f=\omega_c(-Ei_q-Q_f)$$
$$\dot i_d=\omega_{cur}(i_d^s-i_d),\qquad \dot i_q=\omega_{cur}(i_q^s-i_q)$$

一致性:$-E\,i_q^s=(E^2-EV\cos\delta)/X_g=Q_e$ ✓。

$\dot i_q$ 那一行依赖 $\delta,Q_f$ ⇒ $A_{qd}\neq0$ **[证]**,**根本没有块三角**,
GFM 不存在"六态还是八态"的选择。

**$\varepsilon_{qs}$ 精确不变** **[证]**:平衡时 $i=i^s$,故六态平衡点集合是四态
平衡点集合沿 $i=i^s(\delta,Q_f)$ 的图像提升(微分同胚),鞍结点是该集合上两支
合并的性质,与 Jacobian 维数无关。

**[测]** 六态探针(`logs/gfminner.log`),$x=\omega_{cur}/\omega_0$:

| $x$ | $\delta\alpha/\alpha$ (A/B/C/D) | $\delta\omega_0/\omega_0$ | $\delta(ab)/(ab)$ |
|---|---|---|---|
| 1000 | $-0.17/-0.37/-0.29/-0.51\%$ | $\le0.018\%$ | $\le0.12\%$ |
| 100 | $-1.69/-3.67/-2.88/-5.14\%$ | $\le0.17\%$ | $\le1.17\%$ |
| 30 | $-5.7/-12.3/-9.6/-17.2\%$ | $\le0.50\%$ | $\le3.98\%$ |
| 10 | $-17.5/-36.8/-28.8/-51.0\%$ | $\le0.98\%$ | $\le12.69\%$ |

干净的 $O(1/x)$,前因子 $O(1)$(1.7–5.1)。

---

## 7. 为什么同一个电流环在两个对象上后果差三个数量级

GFL 的 $\alpha$ 是一个 $\zeta=0.0031$($Q=\omega_0/2\alpha=162$)的高 Q 模态的
**小实部**,雅可比上 $O(1/x)$ 的扰动落到 $\alpha$ 上被品质因数放大:实测放大
倍数 1080–1146×,即 $\delta\alpha/\alpha\approx1100/x$(`logs/gflinner.log`)。
GFM 临界模态 $\zeta=0.115$–$0.326$,判据建在 $a,b,\varepsilon_{qs}$ 这些 $O(1)$
量上,$O(1/x)$ 进去还是 $O(1/x)$。

代真实带宽($\omega_{cur}\sim2000$ rad/s):GFM $\omega_0=2.7$–$16$ ⇒ $x\approx125$–740,
误差 $\le5\%$;GFL $\omega_0=32.4$ ⇒ $x\approx60$,$\delta\alpha/\alpha\approx18$ 倍。

**更要紧的是 GFL 的 Hopf 越界模态换人**:$\omega$ 由 32.05 变到 58.45($x=100$)、
90.73($x=10$),$P_{Hopf}$ 移 $-4.8\%$ / $-21.5\%$。模态换了,通道二分与驱动
通道绑定的符号审计都要重做。

---

## 8. 定版建议

| 对象 | 默认 | 何时升级 |
|---|---|---|
| GFL | **八态** | 恒用;$i_q^*$ 外生且只要状态轨迹时可用「六态 + 前置 $H(s)$」,但阈值机器仍须用扩展张量 |
| GFM | **四态**($X_g\to X_g+X_v$) | 需要 $\alpha$ 精度优于 5% 时上六态;折叠侧($\varepsilon_{qs}$、$a$、$b$)永不需要 |

强迫一律以参数调制 $u(t)=a\cos\omega_pt$ 进入,通道 $V,P,Q,X_g,\omega_g$;
$V,Q$ 为乘性通道(必须用 §4 的扩展张量),$P$ 为纯加性。

---

## 9. 脚本与日志索引

| 内容 | 脚本 | 日志 |
|---|---|---|
| 八态构建 / 块三角 / 通道 / 电压环首扫 | `scripts/qaxis.py` | `logs/qaxis.log` |
| 乘性项判决性检验 + 电压环符号修正 | `scripts/qaxis2.py` | `logs/qaxis2.log` |
| 四态 V/P/Q 加性 vs 乘性 + 在册数字回代 + GFM 符号判定 | `scripts/qaxis3.py` | `logs/qaxis3.log` |
| 调压支稳定极限与临界增益闭式核对 | `scripts/qaxis4.py` | `logs/qaxis4.log` |
| GFL 五态内环探针($1100/x$) | `scripts/gflinner.py` | `logs/gflinner.log` |
| GFM 六态内环探针 | `scripts/gfminner.py` | `logs/gfminner.log` |
| GFL 权威四态实现 | `scripts/selfhead.py` | — |
| GFM 权威四态实现 | `scripts/gfmlib.py` | — |

## 10. 本文件未覆盖(开放)

- 乘性修正只换了 $c_x$;五阶 $c_{xx},c_{a4}$ 与 kick 的二阶项仍是加性版。
- GFL 带无功/电压环时的阈值机器(八态 + 新临界模态 $\omega\approx43.6$)未重建。
- 限流未建模(用户明确先不考虑)。
- $R_f\neq0$ 时电流环零点位置与本式的差(阶 $R_f/k_{pc}$)未量化。
