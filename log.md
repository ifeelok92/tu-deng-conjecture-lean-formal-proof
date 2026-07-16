# Tu-Deng 猜想攻关进展记录

## 2026-07-16：Tu--Deng 猜想已由独立 first-exit 路线完整证明并经 Lean 核验

1. **当前最终结论已升级：完整 Tu--Deng 猜想已证明。** 新的
   first-exit/cyclic-carry 路线直接证明了对任意 \(k\ge2\) 和 \(t\)，
   \[
   0<t<2^k-1\Longrightarrow
   \operatorname{tuDengCount}(k,t)\le2^{k-1}.
   \]
   Lean 最终定理为
   `TuDengFormal/TuDengFormal/FirstExitNat.lean:530` 的
   `TuDeng.FirstExit.tu_deng_conjecture_full`。全项目 `lake build`
   以 8,591 jobs 成功；`#print axioms` 仅报告 `propext`、
   `Classical.choice`、`Quot.sound`，没有 `sorryAx`，最终路线也不依赖
   `native_decide`。旧 gap/prefix 路线的两个 `sorry` 仍在仓库中，
   但不在该定理的依赖闭包内。

   下述 intrinsic 路线本轮也已严格完整闭合
   \[
   \boxed{N\ge4\Longrightarrow T_4>0},
   \]
   所以该旧路线内的首个开放 intrinsic prefix 仍是 \(T_5\)；
   \(T_5,\ldots,T_N\) 作为更强的中间命题仍未闭合，但它们已不再是
   证明 Tu--Deng 猜想的必要缺口。
2. **任意阶 canonical faces 已建立统一 Pascal 递归。** 若
   \(\Phi(x)=\sum_aP_ax^a\)，则
   \[
   \gamma_r=\sum_{a=0}^r\frac{\binom ra}{\binom Na}P_a,\qquad
   T_k=kP_0+\sum_{a=1}^k
   \frac{\binom{k+1}{a+1}}{\binom Na}P_a.
   \]
   对任意 \(k\)-set \(Q\)，
   root_intrinsic_face_recursive_bridge.md / .py 定义 canonical
   full face \(\Omega_Q^{(k)}\) 与 localized control
   \(\lambda_Q^{(k)}\)，并逐 atom 证明
   \[
   \boxed{
   \Omega_Q^{(k)}=\lambda_Q^{(k)}
   +\frac1{Z-k+1}\sum_{\substack{R\subset Q\\|R|=k-1}}
   \Omega_R^{(k-1)}.}
   \]
   求和即为 \(T_k=T_{k-1}+\gamma_k\)，但局部式保留了已经闭合的
   \(T_{k-1}\) buffer，是后续 \(T_4,\ldots,T_N\) 不必逐层从零重建
   kernel 的统一接口。localized \(\gamma_k\) 不能单独逐面证明：
   \(z=7,N=4\) 已有 \(\lambda_Q^{(4)}=-17/3\)。
3. **任意阶 unit-conditioned buffer 也已统一。** 令
   \(E_j^{(k)}\) 为恰含 \(j\) 个 units 的 full \(k\)-faces 之和，
   \(L_k=\operatorname{lcm}(1,\ldots,k)\)，并置
   \[
   H_k=(L_k-1)E_1^{(k)}+L_k\sum_{j=2}^kE_j^{(k)}.
   \]
   则
   \[
   T_k=E_0^{(k)}+\frac{E_1^{(k)}+H_k}{L_k}.
   \]
   对 \(\lambda^{(k)}\) 定义同权 \(H_{\gamma,k}\)，令 tail 的
   unit/nonunit 数为 \(r,h\)、\(D=Z-k+1\)、
   \(c=L_k/L_{k-1}\)，精确双计数给出
   \[
   \boxed{
   H_k=H_{\gamma,k}
   +\frac{(L_k-1)r}{D}E_0^{(k-1)}
   +\left(c+\frac{k-2-h}{D}\right)E_1^{(k-1)}
   +cH_{k-1}.}
   \]
   除 \(H_{\gamma,k}\) 外的系数在相应 faces 存在时非负。这是把已证低阶
   资源向高阶传递的当前主骨架，不是高阶正性的自动证明。
4. **\(T_4\) 四点 simplex 与第三面 kernel bridge 已精确闭合。**
   root_intrinsic_fourth_face_direct.md / .py 证明
   \[
   T_4=4P_0+\frac{10}{N}P_1+\frac{10}{\binom N2}P_2
   +\frac5{\binom N3}P_3+\frac1{\binom N4}P_4
   =\sum_{|Q|=4}\Omega_Q.
   \]
   取 \(\Omega_Q=2K_4/(N^{\underline4}Z^{\underline4})\)，并令
   \(J_4\) 为五层系数全为 1 的 \(\gamma_4\) kernel，则
   \[
   \boxed{
   K_4(Q)=12J_4(Q)+(N-3)
   \sum_{\substack{R\subset Q\\|R|=3}}K_3(R).}
   \]
   逐四点 full-face 非负严格为假。\(N=4\)、四个连续 internal units、
   \(z=8+y\) 时
   \[
   -K_4=133200+306480\binom y1+258096\binom y2
   +103824\binom y3+16704\binom y4>0.
   \]
   首点 \(\Omega=-185/14\)。所以必须保留跨四点面的全局 buffer。
5. **Tail 全 unit 的 \(T_4\) 已对任意 rank/path 严格为正。**
   root_intrinsic_fourth_face_all_unit_proof.md / .py 使用精确
   root-conditioned path 计数
   \[
   c_{k,\beta}=\binom{k+1}{\beta}
   \binom{z-k-2}{\beta-1}\qquad(1\le k\le4)
   \]
   把全量压成 degree-12 coefficient bracket。\(N\ge12\) 是一张
   155 项、总次数 17、最小系数 \(5/2\) 的普通正系数证书，fingerprint
   为
   7380517f0818aa1eb7af2c1f994e151a9ed63ba5caa6e73c127e0a67a51f62a1；
   \(N=4,\ldots,11\) 是八条覆盖全部 slack 的严格 Newton 行。默认又从
   214,851 张原始 full-\(T_4\) faces 三路核对。因此
   \[
   \boxed{\text{tail 全 unit}\Longrightarrow T_4>0}
   \]
   对全部 \(N\ge4,z\ge N+2\) 成立。
6. **\(N=4\) 的零/单 unit 局部面已对任意 path/depth 严格为正。**
   root_intrinsic_fourth_face_rank_four_local_proof.md / .py 用五个
   cyclic gaps 的零/正模式完备分类 31 个有向稳定 signatures；depths
   精确截断为 \(\{1,2,3,4,I\}\)。31 类乘 512 个至多一 unit depth 类，
   共 15,872 条永久 \(z\)-rays、79,360 个 Newton 系数全部严格为正，
   全局最小系数 432，fingerprint 为
   3b6b7948d2ac3ecb747d3bf1dbcdceb43fba0998fea6f745fb4af6ef1e00c22f。
   cutoff 尖锐：连续 internal 四点在
   \[
   (z,d,\Omega)=(13,(2,1,1,2),-221/594),\
   (11,(1,1,1,2),-2/5),\
   (8,(1,1,1,1),-185/14)
   \]
   分别给出 2/3/4 unit 负面。
7. **\(N=4\) 的恰一 nonunit 全局域已对任意长度/位置/depth 闭合。**
   root_intrinsic_fourth_face_rank_four_one_nonunit_proof.md / .py
   把 root 到唯一 hole 的两条弧截成距离 \(1,2,3,4,\ge5\) 五个永久
   类型。前四个 boundary 类型给出 16 条一维全-slack Newton 行；
   central 类型保留两条独立弧 slack，给出四张二维 simplex 证书。
   合计 104 个严格正系数、36 个零系数、无负系数，最小正系数
   \(19/4\)，fingerprint 为
   d6fd9d0e5df5cf584d73d29756ab8818d35fad2547c5f3191b9c0f9949c7aa14。
   两条弧都至多 4 的唯一有限窗只有 24 个原始状态，最小
   \(T_4=821/3\)。结合 all-unit 与第 6 点，\(N=4\) 的首个剩余 mixed
   域已缩为 tail units、nonunits 均至少两个。
8. **\(N=4\) 的恰二 nonunit 全局域也已参数闭合。**
   root_intrinsic_fourth_face_rank_four_two_nonunit_proof.md / .py
   用 root 与两个 holes 之间三条弧的
   \((\min(a,5),\min(b,5),\min(c,5))\) 作完备 descriptor。61 个含
   capped-5 的无界 descriptors 乘 16 个 depth pairs，共 976 个多元
   slack 族；7,280 个 scaled-simplex Newton 系数中 5,312 个严格正、
   1,968 个为零、无负系数，最小正系数 4，fingerprint 为
   7c50a003986e271b54f913f18a96e10d0d524b578d93d1041507cf8076784828。
   三弧全短的 864 个有限状态最小 \(T_4=611/6\)。故 \(N=4\) 的首个
   剩余 mixed 域进一步推进到 tail units 至少 2、nonunits 至少 3。
9. **当前 \(T_4\) 的正确 global reduction。** 对第四面按 unit 数写
   \(E_0,\ldots,E_4\)，则
   \[
   H_4=11E_1+12E_2+12E_3+12E_4,\qquad
   T_4=E_0+\frac{E_1+H_4}{12}.
   \]
   若 \(F_j\) 与 \(G_3=5F_1+6F_2+6F_3\) 是已证第三面量，则
   \[
   \boxed{
   H_4=H_{\gamma,4}
   +\frac{11r}{Z-3}F_0
   +\frac{2r+h-4}{Z-3}F_1
   +2G_3.}
   \]
   后三项都是已有非负资源。随后完成的 \(N=4\) global moment 证明正是
   保留这些共享资源的联合支付；不要退回逐 \(\gamma_4\)-simplex、逐
   full 四点面或裸 finite-\(z\) 扫描。
10. **\(N=4\) 的 \(H_4\) 已压成唯一四阶联合 moment。**
   root_intrinsic_fourth_face_rank_four_global_reduction.md / .py 从原始
   weighted-\(K_4\)、colour atoms 与 edge-subset moments 三路证明
   \[
   \begin{aligned}
   H_{4,K}={}&1152M_{00}A_z(4)
   +180n(M_{10}P_R+M_{11}P_U)\\
   &+40n(n-1)(M_{20}T_{RR}+M_{21}T_{RU})
   +240n^{\underline4}W_4,
   \end{aligned}
   \]
   其中系数强制的正确联合块是
   \[
   \boxed{
   W_4=T_{UU}+\frac34(Q_{RUU}+Q_{UUU})+\frac35S_{UUUU}.}
   \]
   \(W_4\) 已进一步写成 \(U_{a,k}\) 与 depth-two mixed moments
   \(X_k\) 的精确 induced-edge Newton 式；新增信息只到
   \(U_{4,2},U_{4,3},U_{4,4}\)，不会随 path 长度增长。默认门禁核对
   300 个随机三路状态、18,750 个五-depth-class 小环全状态以及完整
   atom/Newton 表。depth-two pair 块还有尖锐统一界
   \(T_{RR}\ge-42\)，在 12/13 个 depth-two holes 时可取到。
11. **两个早期无界密度锥已严格闭合，并保留为独立支付证书。**
   root_intrinsic_fourth_face_rank_four_high_hole_cone_proof.md / .py
   先证明
   \[
   r\ge2,\ h\ge84r\Longrightarrow H_4>0.
   \]
   它使用 7,936 条 one-unit 与 3,503 条 multi-unit 永久局部 rays，
   再以 \(r=2+x,h=84r+y\) 的 45 项二维 Newton 证书收尾；最小正系数
   166,320，fingerprint 为
   17c1d42fe0223b1d37abee12b0b01573fbd93ad2d79b4cfdcf0bef26eed3f102。
   root_intrinsic_fourth_face_rank_four_large_unit_cone_proof.md / .py
   又用 inactive backbone 的 edge-motif caps 与 active-hole debt
   证明
   \[
   r\ge103,\ h\ge3\Longrightarrow T_4>0.
   \]
   这两条后来被第 12 点更强的全密度定理覆盖，但仍是可独立复核的
   无界证书，不应误写成 fixed-\(h\) 证据。
12. **\(N=4\) mixed 域的任意位置/任意 depth 无界尾已在
   \(n\ge28\) 全密度闭合。**
   root_intrinsic_fourth_face_rank_four_global_moment_bound.md / .py
   把
   \[
   12T_4=B_0(U)+\sum_xM_{d_x}(x)
   +20\sum_{\{x,y\}\subset D_2}(-3)^{E(x,y)}
   \]
   精确拆成 inactive binary backbone、逐 hole 修正和唯一 depth-two
   pair interaction。backbone 只保留三类可能为负的 edge collections，
   并用
   \(N_{12}\le r-1,N_{23}\le3r,N_{34}\le6r\) 支付；全部 hole depths
   共享同一二次下界，pair 块使用第 10 点的 \(-42\)。最终
   \[
   12T_4\ge\mathcal L(r,h).
   \]
   两张 \((r,h)=(25+x,3+y),(2+x,15+y)\) 的 14 项普通正 Newton 锥
   最小系数均为 3；中间只余 66 个 lower-polynomial 参数对，最小值
   \(\mathcal L(23,5)=3666\)。fingerprint 为
   bc88790ff3d8b8c5ea14317bc4419955490beb03af7f4988a52b42b7e6424143。
   因而严格得到
   \[
   \boxed{r\ge2,\ h\ge3,\ n=r+h\ge28\Longrightarrow T_4>0.}
   \]
13. **有限窗不是 word 穷举，而由 global \(\gamma_4\) unit-insertion
   自动机完整闭合。**
   root_intrinsic_fourth_face_rank_four_gamma_window_proof.md / .py
   使用 \(R_1-I=ce_2^T\) 把 unit 插入差闭合成
   \(X_0,\ldots,X_4,Y_0,\ldots,Y_4\) 十维整数自动机。对完整字母表
   \(\{1,2,3,4,I\}\)，长度 \(4,\ldots,31\) 的全部可达状态均满足
   \(Y_0,\ldots,Y_4\ge0\)；状态数从 159 增到 786,738，完整 fingerprint
   为
   60fe144130896794fe650745652ff626ad77c762f2621b8c71aaf314b935d2da。
   反射严格处理插入点左右方向：插入后 \(n\ge8\) 时旧 word 的一侧至少
   长 4；\(n=5,6,7\) 的 96,875 个原始 bases 最小值分别为
   11/38/61。另对任意长度 all-nonunit word 证明
   \(\gamma_4>0\)，最终 Newton 行为 \((223,110,36,8,1)\)。
   因此
   \[
   \boxed{5\le n\le31\Longrightarrow\gamma_4>0.}
   \]
   与已证 \(T_3\ge0\) 拼接即得该窗 \(T_4>0\)。
14. **完整 \(N=4\) 第四面已经严格闭合。**
   root_intrinsic_fourth_face_rank_four_complete_proof.md / .py 把
   零/单 unit 局部定理、all-unit、恰一/恰二 nonunit、第 12 点的
   \(n\ge28\) global theorem 与第 13 点的 \(n\le31\) gamma theorem
   无缝路由。默认完整门禁重建全部 locked certificates，遍历 20,286 个
   \((n,r,h)\) 路由状态，并输出
   \[
   \boxed{N=4\Longrightarrow T_4>0}
   \]
   对任意 path 与 depth word 成立。两份独立审计分别重建 global
   atom/moment 下界和 gamma insertion 自动机，结论均为 PASS。
   所以一般第四面的首个开放 rank 现在是 \(N\ge5\)，不再是任何
   \(N=4\) mixed 子域；一般 \(T_4\)、\(T_5,\ldots,T_N\) 与完整
   Tu--Deng 猜想仍然开放。
15. **\(N=5\) 的低复杂度边界已全部参数闭合。**
   root_intrinsic_fourth_face_rank_five_local_proof.md / .py 用 31 个稳定
   gap signatures 与 1,125 个至多一 unit depth 类生成 34,875 条永久
   rays；209,250 个 Newton 系数全部严格为正，最小值 2,160，fingerprint
   为
   e52f78629af58d4d8acab13605eae4e0bdce91b1190a4533ca746939d22bcba2。
   两个 units 已有尖锐局部反例
   \(\Omega(18;(2,1,1,2))=-3667/7140\)，所以仍必须保留 global buffer。
   root_intrinsic_fourth_face_rank_five_one_nonunit_proof.md / .py 与
   root_intrinsic_fourth_face_rank_five_two_nonunit_proof.md / .py 又分别以
   两弧/三弧永久 simplex Newton 证书闭合恰一、恰二 nonunits 的任意长度、
   位置与 depths；fingerprints 为
   53eee77c0e61a979e536882f9f1e97b73b2b1c19eaf51b6c7692a1ce14e7371f
   与 b8ed20207ca9e4227c48884a3599589d80f0ca9954331613f38deb2079ccf903。
   因而 \(N=5\) 的唯一剩余 mixed 域精确缩为 \(r\ge2,h\ge3\)。
16. **\(N=5\) 的 exact hole decomposition 与大长度基线已经建立。**
   root_intrinsic_fourth_face_rank_five_global_moment_bound.md / .py 证明
   \[
   10T_4=B_0(U)+\sum_xM_x(d_x)+\sum_{x<y}I_{xy}(d_x,d_y),
   \]
   crossing-hole 只有 \((2,2),(2,3)\) 两类。inactive backbone 用八类
   edge-collection moments 重建，三类负 motifs 由
   \(N_{12}\le r-1,N_{23}\le3r,N_{34}\le6r\) 支付；第一版无界证书先得到
   \(n\ge262\Rightarrow T_4>0\)，fingerprint 为
   4817d7c377f635263b24ea7777fdcdab125d8a91438d6a595acb2ce725a5bb66。
   另 root_intrinsic_fourth_face_rank_five_gamma_insertion_bridge.md / .py
   建立 \(\gamma_4=\Phi(1)-\Phi'(1)/5\) 的一阶 jet 插入恒等式与 17 维
   sufficient cone，并证明 all-nonunit \(\gamma_4>0\) 对任意长度成立；
   该桥是严格接口，但没有被冒充成任意长度 cone invariant。
17. **endpoint-unit 条件化把 \(N=5\) mixed 无界阈值从 262 降到 13。**
   root_intrinsic_fourth_face_rank_five_global_sharpened_proof.md / .py
   只让真正被 cycle edge 触及的 unit subsets 支付 hole 负债，并保留
   endpoint-unit 数 \(b\) 强制产生的正 support-one backbone motif。
   Internal/endpoint 的 affected-subset caps 分别使用 boundary 4/2；
   \(I_{22}\) 按 induced-edge 数保留
   \(L_0=10n-5r-210,L_1=-30n+15r-50,L_2=90n-45r-690\)，而
   \(I_{23}\) 的负块由 \(-90h\) 支付。\(b=1\) lower 是 \(b=0,2\)
   两角点的精确中点，故只余三个 endpoint 角点乘 \(L_0\) 两分支。
   \(L_0\ge0\) 由三张 20 项 cone 加每角点 34 条永久 rays 闭合；
   \(L_0<0\) 只有 270 个 lower-polynomial 参数态。六支全局最小值
   39,696，fingerprint 为
   ca0d6effa31a60b529198a0a32a2cd839b20526e215d6a5e51fc85155ab9e7f2。
   因而严格得到
   \[
   \boxed{N=5,\ r\ge2,\ h\ge3,\ n\ge13\Longrightarrow T_4>0.}
   \]
18. **完整 \(N=5\) 第四面已经严格闭合。**
   root_intrinsic_fourth_face_rank_five_finite_bridge.md / .py 利用只有
   \(22/23\) crossing pairs 的截断，把每个 nonunit 精确压成
   \(\{2,3,O\}\) 三态。对 \(6\le n\le12\) 的 7,722 个 binary masks
   完整遍历 18,513,630 个 leaves；全局最小 witness 为
   \((1,5,4,4,5,1)\)，且 \(T_4=200\)。fingerprint 为
   f1363c921b009f143448756a98cb58f84040ac43dcbd9beab8f8534906a80d1c。
   root_intrinsic_fourth_face_rank_five_complete_proof.md / .py 将 local、
   all-unit、one/two-nonunit、finite \(n\le12\) 与 global \(n\ge13\)
   六分支无缝路由，严格得到
   \[
   \boxed{N=5\Longrightarrow T_4>0}
   \]
   对任意 path/depth word 成立。独立审计
   root_intrinsic_fourth_face_rank_five_complete_review.md / .py 不导入
   finite/global 被审核心函数，从 raw controls/atoms 重建 18,513,630 个
   finite leaves、global motifs/caps/六支 Newton 与 501,480 个路由状态，
   结论 PASS；review fingerprint 为
   73e5d861f962fbaa2215da26b2b60206fee8c071a3ce221e06377c62b330308e。
   所以一般第四面的首个开放 rank 已推进到 \(N\ge6\)。
19. **\(N=6\) 已建立 exact triple-hole 接口并闭合低复杂度边界。**
   root_intrinsic_fourth_face_rank_six_reduction.md / .py 给出最小整数缩放
   \[
   60T_4=240P_0+100P_1+40P_2+15P_3+4P_4
   \]
   及 inactive + unary + pair + triple-hole 精确分解。pair 新增
   \((2,4),(3,3)\)，并首次出现唯一三-hole 块
   \(R_{xyz}\ne0\iff(d_x,d_y,d_z)=(2,2,2)\)；71,280 个截断 atom 状态的
   fingerprint 为
   f95cfc220826e51989dc11efac817c559d51bb7d16f700ae90b84d0c6c334248。
   root_intrinsic_fourth_face_rank_six_progress.md / .py 又闭合至多一 unit
   的全部局部面，以及恰一/恰二 nonunits 的任意长度全局域，把当时首剩域
   精确缩成 \(r\ge2,h\ge3\)。后续完整证明确实显式保留了新增 \(222\)
   三体项，不能把本条历史中间状态误写成当前缺口。
20. **完整 \(N=6\) 第四面已经严格闭合。**
   root_intrinsic_fourth_face_rank_six_finite_bridge.md / .py 对
   \(7\le n\le13\) 的 15,773 个 unit masks 精确遍历 77,116,941 个
   reduced states，最小 \(60T_4=36,480\)，fingerprint 为
   32d27bed2886b9e5605a9fa8d9940eb71ee2146ba405620388b5c317ef7c49a3。
   root_intrinsic_fourth_face_rank_six_global_moment_bound.md / .py 再以
   endpoint-conditioned backbone、edge-touched unary/pair caps 与共享
   \(222\) triple buffer 证明
   \[
   n\ge14,\ r\ge2,\ h\ge3\Longrightarrow T_4>0.
   \]
   其最终 fingerprint 为
   128cd67ac072db3d8d8b6c413b532cf313f453ab12a3184c74dc15b2c1d5fe2a；
   特别补齐了 \(E=2\) pair 分支 \(h=3,\ldots,6\) 的 16 条横向永久
   rays。root_intrinsic_fourth_face_rank_six_complete_proof.md / .py 将六路
   参数域无缝拼接，严格得到
   \[
   \boxed{N=6\Longrightarrow T_4>0}.
   \]
   finite/global 两份独立审计 fingerprints 分别为 fec6d4f5... 与
   6d9ca1c6...；完整 router 覆盖 501,473 个参数态且每态恰命中一支。
21. **\(N=7\) 的 exact reduction 与低复杂度边界已经闭合。**
   root_intrinsic_fourth_face_rank_seven_reduction.md / .py 证明最小整数缩放
   为 105，五层权重为 \((420,150,50,15,3)\)，depth cutoff 为 \(I=8\)。
   Pair types 是 \(22,23,24,25,33,34\)，pair+unit 是
   \(22,23,24,33\)，pair+two-unit 是 \(22,23\)；triple 是
   \(222,223\)，triple+unit 只有 \(222\)，四-hole block 恒为零。
   457,968 项表 fingerprint 为
   3d5c239ce366f80431d5b6af543bc1212da36b8a3f4e479a64e9d1bd70ed1ce4。
   root_intrinsic_fourth_face_rank_seven_progress.md / .py 又以 116,963 条
   local rays 和 35/2,989 个 one/two-nonunit 永久 families 闭合
   \(r\le1\) 或 \(h\le2\) 的全部参数域，真实首剩域缩成
   \(r\ge2,h\ge3\)。
22. **\(N=7\) 的最后 mixed 域已经严格闭合。**
   root_intrinsic_fourth_face_rank_seven_mixed_complete_proof.md / .py 在
   \(8\le n\le13\) 固定真实 unit positions，以 block-level
   edge-touched envelopes 一次消去任意 depths；15,682 个 masks 的最小
   scaled lower 为 185,250。对 \(n\ge14\)，证明保留 endpoint-unit 数、
   八类 inactive moments、六种 joint pair blocks 和 \(222/223\) shared
   triple buffer。稳定域的三个 endpoint corners 各有一张 35 项、
   total-degree-7 正系数 cone 及完整低参数 rays；\(14\le n\le17\) 的
   138 个 boundary corners 最小 lower 为 10,239,552。必须按 \(r\) 保留
   \(n=14\) 的 \((2,3)\) motif 变号，不能统一当成负项。联合 fingerprint
   为
   8822d15c4fc7c728f908efa4d43fbafa6e156305704ad2431a3d3124db96f98d。
23. **完整 \(N=7\) 第四面已经严格闭合，当时首缺口推进到 \(N\ge8\)。**
   root_intrinsic_fourth_face_rank_seven_complete_proof.md / .py 将 all-unit、
   one/two-nonunit、低 unit local 与 mixed complete 五支无缝路由，得到
   \[
   \boxed{N=7\Longrightarrow T_4>0}.
   \]
   独立审计 root_intrinsic_fourth_face_rank_seven_complete_review.md / .py
   不导入 mixed/complete 被审核心函数，重建 finite envelopes、全部
   atom/motif/unary/pair/triple Newton domains、三个 endpoint corners、
   500 个 raw identities 与 501,465 个 router states；独立 review
   fingerprint 为
   23075a8f3d9bb4bf01a07206e8b5f30c69373179eedb7340e2d32d5b16a52d70。
   所以该阶段一般第四面的第一个开放 rank 是 \(N\ge8\)；这仍不证明一般
   \(T_4\)、\(T_5,\ldots,T_N\) 或完整 Tu--Deng 猜想。
24. **\(N=8\) 的 exact reduction 与低复杂度边界已经严格闭合。**
   root_intrinsic_fourth_face_rank_eight_reduction.md / .py 证明最小整数缩放
   为 280，五层权重为 \((1120,350,100,25,4)\)，depth cutoff 为 9。
   Crossing catalogue 含九种 pair、六种 pair+unit、四种 pair+two-unit、
   四种 triple、两种 triple+unit，并首次出现 genuine \(2222\)
   quadruple；727,496 项截断表 fingerprint 为
   2cc9a3dbdaf427c68523e69a6018da9ccfcb16b7e98bc464200c02101b6818d7。
   root_intrinsic_fourth_face_rank_eight_progress.md / .py 又以 190,464 条
   local rays、40 个 one-nonunit 和 3,904 个 two-nonunit 永久 families
   闭合 \(r\le1\) 或 \(h\le2\)，把唯一剩余域缩成 \(r\ge2,h\ge3\)。
25. **\(N=8\) 的 mixed 域已经严格闭合，并正确吸收 genuine quadruple。**
   root_intrinsic_fourth_face_rank_eight_mixed_complete_proof.md / .py 在
   \(9\le n\le14\) 以 position-exact block envelopes 覆盖 31,735 个
   unit masks，最小 scaled lower 为 1,688,619。对 \(n\ge15\)，证明保留
   endpoint-conditioned inactive moments、13 个 unary、27 个 joint pair、
   18 个 shared triple 分支以及 \(2222\) quadruple 的 path cap。
   Endpoint depth three 不能局部丢弃；正确共享下界是
   \(H_3^{\rm end}\ge-10n^4\)，故必须增加 \(b=0\) 的
   \(-20n^4\) corner。四个 stable corners 都是 44 项、总次数 8、最小
   系数 35 的正 Newton cone；\(15\le n\le20\) 的 324 个 boundary
   corners 最小 lower 为 113,590,536。主 fingerprint 为
   dd7230bee95c84f7822df01d3d6f27c5199688d51422c94609b67e2bda61d80c。
26. **完整 \(N=8\) 第四面已经严格闭合，当时首缺口推进到 \(N\ge9\)。**
   root_intrinsic_fourth_face_rank_eight_complete_proof.md / .py 将 all-unit、
   one/two-nonunit、低 unit local 与 mixed complete 五支无缝路由，默认
   全量门禁退出码为 0，严格得到
   \[
   \boxed{N=8\Longrightarrow T_4>0}.
   \]
   独立审计 root_intrinsic_fourth_face_rank_eight_complete_review.md / .py
   不导入 mixed/complete 被审核心函数，重建 finite envelopes、全部
   atom/motif/hole/pair/triple/quadruple 证书、literal path caps、500 个
   raw identities 与 501,456 个 router states；review fingerprint 为
   4c806b60fdc2202f1ba488e642d010bb3e16e3a5f4f9dba6c84341956b98bf0d。
   因而该阶段一般第四面的第一个开放 rank 是 \(N\ge9\)。一般 \(T_4\)、
   \(T_5,\ldots,T_N\) 与完整 Tu--Deng 猜想仍然开放。
27. **\(N=9\) 的 exact reduction 与低复杂度边界已经严格闭合。**
   root_intrinsic_fourth_face_rank_nine_reduction.md / .py 证明最小缩放为
   252、五层权重为 \((1008,280,70,15,2)\)、depth cutoff 为 10；
   crossing catalogue 新增 \(27,36,45\)、\(225,234,333\) 与第二种
   quadruple \(2223\)。1,092,906 项截断表 fingerprint 为
   2776623e6775d65e9a34af7771fd48238f89bedda02f89c03e124f1f218e7c43。
   root_intrinsic_fourth_face_rank_nine_progress.md / .py 以 293,787 条
   local rays、45 个 one-nonunit 和 4,941 个 two-nonunit 永久 families
   闭合 \(r\le1\) 或 \(h\le2\)，唯一剩余域仍为 \(r\ge2,h\ge3\)。
28. **\(N=9\) 的 mixed 域已对任意 path/depths 严格闭合。**
   root_intrinsic_fourth_face_rank_nine_mixed_complete_proof.md / .py 在
   \(10\le n\le16\) 以 129,292 个 position-exact unit masks 消去任意
   depths，最小 scaled lower 为 5,164,452。对 \(n\ge17\)，证明保留
   endpoint-conditioned moments、15/36/30 个 hole/pair/triple 联合块，
   并以 10 条永久 rays 同时支付 \(2222,2223\)：零边 branches 非负，
   affected branches 统一不小于 \(-54(n-9)\)。三个 endpoint corners 在
   \(r=21+x,h=30+y\) 上各给出 54 项、总次数 9、最小系数 28 的严格
   正 cone；279 个 boundary corners 最小 lower 为 598,689,030。主
   fingerprint 为
   67ac82d8d412ddc2279411fa734a3b11b280f0dd86d0fc47420ef1b9b2e38f82。
29. **完整 \(N=9\) 第四面已经严格闭合，首缺口推进到 \(N\ge10\)。**
   root_intrinsic_fourth_face_rank_nine_complete_proof.md / .py 以五路完备
   router 拼接全部参数域，严格得到
   \[
   \boxed{N=9\Longrightarrow T_4>0}.
   \]
   独立审计 root_intrinsic_fourth_face_rank_nine_complete_review.md / .py
   不导入 mixed/complete 被审核心函数，重建 129,292 个 finite masks、
   全部 atom/motif/hole/pair/triple/quadruple Newton 分区、2,926 个 literal
   graph states、300 个 raw identities 与 501,446 个 router states；
   review fingerprint 为
   4ec90d4729c0b5c8d45b45a39bd517f07280bf56e2b6d6091f7aff0e6d6576da。
   因而一般第四面的首个开放 rank 现在为 \(N\ge10\)。一般 \(T_4\)、
   更高 intrinsic prefixes 与完整 Tu--Deng 猜想仍然开放。
30. **\(N=7,8,9\) 之间的共同结构已提升为一般-rank factorial bridge，且
   所有未来 pure-hole quadruple frontier 已永久吸收。**
   root_intrinsic_fourth_face_general_rank_factorial_bridge.md / .py 取统一缩放
   \(\mathcal M_4=12\binom N4T_4\)，得到五层多项式权重
   \[
   \bigl(2N^{\underline4},\ 5(N-1)(N-2)(N-3),\
   10(N-2)(N-3),\ 15(N-3),\ 12\bigr),
   \]
   并对任意 \(N\ge4\) 逐 subset 证明 exact
   inactive + unary + pair + triple + quadruple decomposition。固定物理
   slack \(s=n-N-1\) 后，全部 atoms 落在
   \[
   F_q(N,s)=\operatorname{Bal}(N+s+2,N-q)
   =\frac{s+q+1}{N+s+1}\binom{2N+s-q}{N-q}
   \]
   上，旧坐标严格满足
   \[
   F_q(N+1,s)=
   \frac{(2N+s-q+2)(2N+s-q+1)}
   {(N+s+2)(N-q+1)}F_q(N,s).
   \]
   每次升 rank 的新 equality frontier 为
   \(A_N(n,a,N,E)=(-1)^{a+2-E}3^E\)。因此 size four 的新 edge row
   恒为 \((12,-36,108,-324,972)\)，结合 path affected cap
   \(C_4(h)=\min\{\binom h4,(h-1)(h-2)(h-3)\}\) 得到
   \[
   12\sum_{Q\in\mathcal F}(-3)^{E(Q)}\ge-324C_4(h)
   \]
   对任意新 frontier subfamily 成立；它一次覆盖 \(2222,2223\) 及以后
   所有 four-part depth partitions。另一方面最小状态
   \((N,s,a,D,E)=(4,0,2,2,2)\) 有 atom rank lift \(1\mapsto-4\)，严格
   排除 atomwise 正锥，后续必须在全局 shared buffer 上归纳。默认门禁核对
   38,640 个 atom factorial identities、30,826 个 literal path masks、
   400 个 raw controls/decomposition 状态；fingerprint 为
   9db619cbdccc552e195222c9a95c8260c0576036e111d26ae414b38fff1a87d7。
   独立审计
   root_intrinsic_fourth_face_general_rank_factorial_bridge_review.py 不导入
   bridge 模块，从原始 controls、ballot 与自行卷积 kernel 重建全部接口，
   review fingerprint 为
   f80ab8cb3f380324094da2167298f63a607a5d1ee8ccf46cb18bde8cf74aba71。
   这是真正的一般-rank 接口但不是一般 \(T_4\) 正性证明；在该阶段首缺口为
   \(N\ge10\)。后续目标是把 persistent diagonal coordinates 与 frontier
   debt 一起嵌入 endpoint-conditioned global buffer，而不是继续手写
   fixed-rank catalogues。
31. **一般-rank persistent atom 已形成四阶 endpoint-conditioned 全局接口。**
   root_intrinsic_fourth_face_general_rank_persistent_atom_cone_proof.md / .py
   把所有 hole-containing atoms 统一写成 ballot factorial coordinate 加
   非负二元 Newton surplus；40 条原子行的主 fingerprint 为
   f1a77d90c8be7263aa521be9faf67971d4ab7f5d99cb2dc3113ac04cc27493fc，
   独立 review fingerprint 为
   79c991331f7fa6e44c2457ada956244d61b970bf4bf09b9b0442ea96b8b70547。
   三阶截断并不足够：
   \(N=30\) alternating 状态给出严格负的 cubic lower；因此
   root_intrinsic_fourth_face_general_rank_quartic_buffer.md / .py 保留四阶
   surplus，建立八类有限 edge-collection shape 的精确展开，并证明
   endpoint/transition 纯色 caps。其 fingerprint 为
   0b80cc0b4d2769133eeebd019e06208d2c9b56752e0be07586fcc7267d94dc57。
   进一步的 quartic edge cone 与 arbitrary-depth envelope 分别锁定 26 条
   higher-edge 正差分行及逐 \((a,j,E)\) depth-sum 最小化；fingerprints 为
   b4bf2247fa879ff9303dd8397640a57addf1743695d6fefb52f0820be485448d
   与 00968551b313a0dcda9f110b8e3fba0a12e3aa7c26cbf5a9aaa4ff3693eeaed4。
   unary wandering frontier 又由
   root_intrinsic_fourth_face_general_rank_unary_depth_frontier_proof.md / .py
   对全部 \(N\ge30\) 以 root inactive buffer 的四分之一统一支付，fingerprint
   为 a7e49f35423c553e3ae9dddc7df6fb9c4e93f93c3baceda22b42c97b49e423b0。
   这些是严格 reduction/局部支付定理，但 endpoint lower 的一般
   \((N,r,h,s)\) 正锥尚未闭合，不能写成一般 \(T_4\) 已证。
32. **完整 \(N=10\) 第四面已经严格闭合。**
   root_intrinsic_fourth_face_rank_ten_complete_proof.md / .py 不再枚举 depth
   partitions，而是对每个 \((a,j,E)\) 取 exact raw depth-sum envelope。
   \(s\ge21\) 后 envelope 与 54 个 edge-coordinate signs 稳定；order-zero
   与 one-edge 块精确保留，higher edges 以 endpoint-conditioned caps 支付。
   transition lower 关于 \(\tau\) 凹，故只需两个可行端点。无界域由三张
   minimum-transition、三张 unit-limited 与三张 hole-limited 二元正锥，全部
   低密度 Newton rows 和两条 monochrome rows 闭合；2,478 个非零系数的
   最小值为 252。\(0\le s\le20\) 的 2,352 个参数态最小 lower 为
   166,599,455。主 fingerprint 为
   cf97b641aeb9f7c2635ce5e6bd297feaed33fd31c1a15d3b6d8221e198c16c77。
   独立审计
   root_intrinsic_fourth_face_rank_ten_complete_review.md / .py 不导入被审核心，
   从 ballot、cyclic kernel、edge shapes/caps 与另一套 forward differences
   重建全部证书，额外验证最高差分为零；196,416 个 literal cap checks 与
   300 个 arbitrary-depth raw states 全部 PASS，review fingerprint 为
   420f9cfc9c50c70431eecb10a04b5b64393bb45be172afcf716b008ad7f0629a。
   因而严格得到
   \[
   \boxed{N=10\Longrightarrow T_4>0},
   \]
   当前首缺口正式推进到 \(N\ge11\)。下一目标是把 rank-ten 稳定 envelope、
   sign partition 与九张 endpoint cones 提升为带 \(N\) 的统一正锥，而不是
   复制一份 fixed-rank \(N=11\) catalogue。
33. **单一 rank-parameterized 生成器已经完整闭合 \(N=11,\ldots,29\)。**
   root_intrinsic_fourth_face_rank_eleven_to_twentynine_complete_proof.md / .py
   对每个 rank 取 \(s_0=2N+1\)，以 exact raw depth-sum envelope 证明共同
   稳定奇偶模式及同一组 23 个负 edge coordinates。随后用统一的三张
   minimum-transition、三张 unit-limited、三张 hole-limited cones、所有
   density boundary rows 和 monochrome rows 闭合 \(s\ge s_0\)；低 slack
   仍只遍历 \((N,s,r,h,b,\tau)\) 参数而非 words/depth partitions。全区间有
   11,875 条 depth rows、1,026 条 sign rows、192,842 个非零 stable
   coefficients，最小值 360；194,408 个 finite states 的最小 lower 为
   921,638,712。主 fingerprint 为
   c3e5d86b1d38940451a4363d8630e6a7ef286bfc566f58bfb23c599647645fe4。
   独立审计
   root_intrinsic_fourth_face_rank_eleven_to_twentynine_complete_review.md / .py
   不导入主生成器，从 ballot/cyclic kernel 重建全部证书，并额外完成
   89,414 条 transition 二阶差分凹性检查；review fingerprint 为
   acf8286f40f812ee71b9ffa33940da8e6454d3886f832b606b964fb339105af2。
   因而严格得到
   \[
   \boxed{4\le N\le29\Longrightarrow T_4>0},
   \]
   一般第四面的首缺口推进到 \(N\ge30\)。下一步必须接入已证的
   \(N\ge30\) unary wandering-frontier payment 与一般 quartic edge cone，
   闭合真正的 infinite-rank endpoint buffer。
34. **一般 intrinsic 第四前缀已经对任意 rank/path/depth word 严格闭合。**
   root_intrinsic_fourth_face_general_rank_infinite_depth_proof.md / .py 把
   \(N\ge30\) 的任意 depths 压成 27 条统一 adjacent diagonals、两条 exact
   pair diagonals、两类 Catalan low-residual frontier comparisons 和四条
   persistent coarse rows；29 条 \(s=0\) first-step rows 全部为正。无效的
   finite-gap bridges 已删除，depth fingerprint 为
   86d0130f7c78206d9d62a1d7c0b7fd7a973c82ba9e35885b851443dfd9b6a447。
   unary debt 只消耗实际比例 \(h/(4n)\) 的 inactive base。

   root_intrinsic_fourth_face_general_rank_infinite_cone_proof.md / .py 又对
   \(s\ge1\) 证明 26 条 higher-coordinate signs、1,038 个 transition
   curvature identities、三张 minimum-transition 与六组 maximum-transition
   四维 cones、全部 low-density rows 和 monochrome rays；513,957 个非零
   系数的最小值为 195,084,288,000，fingerprint 为
   7f3ffb2fb038877c334fd40342b918d320cd87865acb01bf190d45ac827bbba7。
   独立 Catalan-top 证明有 54 条 sign rows（29 个负 coordinates）、3,795
   个 endpoint-cone coefficients，fingerprint 为
   3b73e8761ed739408b801b45371b436737724df3e81ebd021e56e2d03b38e504。

   root_intrinsic_fourth_face_general_complete_proof.md / .py 最终拼接既有
   \(4\le N\le29\) 定理与 \(N\ge30\) infinite cones，并从 raw
   \(\mathcal M_4=12\binom N4T_4\) 核对 212 个 adversarial/random arbitrary-depth
   states；总 fingerprint 为
   5e0f9d90e7289b41d4768cfeeff63bdacc33bc5adffa7c75cc1b3d248f52ec2d。
   独立审计 root_intrinsic_fourth_face_general_complete_review.md / .py 不导入
   depth/cone/top/complete 主模块，以反向轴 Newton transform 和每轴额外一阶
   degree-exhaustion 重建 541,066 个非零系数（最小值 6），并核对 300 个 raw
   arbitrary-depth states；review fingerprint 为
   ea5a32360300ef793f9f288d00c5fa63f7a972a8cec51f9367f11d7201367957。
   第一次 review 曾抓到审计器自身 all-unit 长度的 off-by-one，修正为
   \(N+s+1=32+q+p\) 后从头全量重跑 PASS。因此严格得到
   \[
   \boxed{N\ge4\Longrightarrow T_4>0}.
   \]
   在这条 intrinsic 路线内，首个开放 prefix 是 \(T_5\)，
   \(T_5,\ldots,T_N\) 与一般 root-anchor 仍然开放。但完整
   Tu--Deng 猜想已由下一条的独立 first-exit 路线证明，不依赖
   这些更强的 intrinsic 中间命题。

35. **独立 first-exit/cyclic-carry 路线已给出完整 Tu--Deng 定理。**
   形式化主链由 `FirstExitCore.lean`、`FirstExitBoundary.lean`、
   `FirstExitPolynomial.lean`、`FirstExitFunctional.lean`、
   `FirstExitCarry.lean`、`FirstExitNat.lean` 六个文件组成，六者均无
   `sorry`/`admit`。关键节点为：

   - `FirstExitPolynomial.lean:457` 的 `cross_boundary_identity`；
   - `FirstExitCarry.lean:761` 的 `cyclicInputCount_bound_of_nonconstant`；
   - `FirstExitNat.lean:499` 起的 `tdFinset_card_eq_cyclicPairs` 精确双射/基数恒等式，
     以及紧接着 `FirstExitNat.lean:512` 的
     `tuDengCount_eq_cyclicInputCount`，它们将原模计数与循环进位计数
     精确连接；
   - `FirstExitNat.lean:530` 的最终定理
     `tu_deng_conjecture_full (k t : ℕ) (hk : 2 ≤ k)`。

   2026-07-16 独立门禁重跑 `lake build` 得到
   `Build completed successfully (8591 jobs)`。Lean 直接公理审计得到
   \[
   \boxed{[\texttt{propext},\ \texttt{Classical.choice},\ \texttt{Quot.sound}]},
   \]
   因而旧模块中的 `sorry` 和有限 `native_decide` 结果都没有渗入
   最终定理。这是与 gap/intrinsic-prefix 路线不同的直接证明；
   后者可继续作为结构性强化研究，但不再决定猜想本身的完成状态。

## 2026-07-14：Intrinsic 第三面已对任意 rank 完整闭合；首缺口推进到 \(T_4\)

1. **完整 Tu--Deng 猜想仍未证明。** 任意 rank/path/depths 的
   intrinsic 第三前缀现已严格闭合：\(N\ge3\Rightarrow T_3\ge0\)。
   与已证的 \(T_1,T_2\) 拼接后，intrinsic prefix bridge 的首个开放
   缺口推进到 \(T_4\)；仍必须统一证明 \(T_4,\ldots,T_N\)，才能
   推出完整 root-anchor。固定 short-gap 主线的严格门槛仍只是
   “最小反例至少六短”，不能因 \(T_3\) 的闭合自动升级。
2. **任意旧 depths 的 I+II+II 联合增量已经参数闭合。** 令
   \(r=N-d_0-d_1-d_2\)、\(q_k=r+d_k\)。
   `root_intrinsic_third_face_joint_increment_proof.md` 对全部真实 path
   signatures、全部二元方向 \(|I|=2\) 证明
   \[
   q_k\ge2\ (k=0,1,2)
   \Longrightarrow
   K(z,N+2;\mathbf d+\mathbf1_I)-K(z,N;\mathbf d)
   >\frac5{2692}\mathcal H>0.
   \]
   精确 atom 分解是 \(9\mathcal H\) 加三个 singleton 与三条
   pair/triple 块；43 张 fixed 证书、48 个任意长度递推恒等式、1,944 个
   factorial normalization 和 45 行真实 signature 预算全部通过，最弱预算
   恰为 \(5/2692\)。默认又从原始 full kernel 核对 168,750 个
   \(r\ge1\) 状态和 195,750 个一般 \(q_k\ge2\) 状态。这个定理使用一条
   Type-I 与两条 Type-II 的**联合 buffer**，没有恢复已被推翻的
   individual Type-II。
3. **全部 non-\((1,1)\) pair 本体和负 residual 窗已经闭合。**
   `root_intrinsic_third_face_nonunit_negative_residual_proof.md` 新生成三张
   \((1,2)\) base 证书（75/74/75 项，总次数 12，最小系数 48/9/16），
   再用已证一坐标传播得到
   \[
   (d,e)\ne(1,1)\Longrightarrow F_{uv}\ge0
   \quad\text{for every integer pair residual }q,
   \]
   且 \(q\ge1\) 时严格为正。与 \(q\le0\) 旧定理拼接后，至多一个 unit
   的 full face 在整个 \(r<0\) 域非负；原先的
   \(-d_{\max}<r<0\) 中间窗还严格为正。85,015 个传播 pair 状态和
   296,817 个原始 full-\(K\) 状态只用于恒等式回归。
4. **物理域内“至多一个 unit”的每张 full-\(T_3\) 局部面现已全部闭合。**
   `root_intrinsic_third_face_nonunit_k_ray_proof.md` 先以 two-track
   rising-product 证书闭合任意长 \((1,2,k)/(2,2,k)\) bases；
   `root_intrinsic_third_face_nonunit_complete_proof.md` 再补上
   \(r=0,q=1\) 的唯一原子边界（一张 35 项、总次数 7、最小系数
   \(1/24\) 的证书），并用精确 depth-lattice 可达性把第 2 点的联合增量
   从两条 base rays 传播到任意 depths。最终严格得到
   \[
   N\ge3,\ z\ge N+2,\ \#\{i:d_i=1\}\le1
   \Longrightarrow K(z,N;d_0,d_1,d_2)\ge0,
   \]
   \(r\ge0\) 时还严格为正。非物理外推是假的：
   \((z,N,d)=(4,3,(1,2,2))\) 有 \(K=-72\)。因此现在可逐面丢弃
   所有零 unit 和单 unit faces。
5. **一般 \(T_3\) 已精确缩成一个全局 unit-count 量。** 令 \(F_j\) 为
   恰含 \(j\) 个 unit 的全部三点面之和。第 4 点给出
   \(F_0,F_1\ge0\)。conditioned-star 的精确计数给出
   \[
   G:=5F_1+6F_2+6F_3,\qquad
   T_3=F_0+\frac{F_1+G}{6}.
   \]
   所以当前第三面的真正充分目标只是 \(G\ge0\)，不必逐 root 证明
   \(W_u\ge0\)。`root_intrinsic_third_face_global_unit_reduction.md` 又把
   它严格压成
   \[
   \begin{aligned}
   G_K={}&5r\sum_{RR}F+[5(h-1)+6(r-1)]\sum_{RU}F
      +6(n-2)\sum_{UU}F\\
      &+3Z(Z-1)(Z-2)(5Q_{RRU}+6Q_{RUU}+6Q_{UUU}).
   \end{aligned}
   \]
   前两组 pair \(F\) 已由第 3 点证明非负；unit--unit 块精确依赖
   \((r,b,e,c_2)\)，而 \(Q_{UUU}\) 还需要三阶 path moments
   \((a,\ell_2,c_3)\)。4,000 个 literal/atom/pair 三路状态和 12,304 个
   unit masks 已精确核对。
6. **全 unit 与 one-nonunit 域已经对全部参数严格为正。**
   `root_intrinsic_third_face_all_unit_proof.md` 对 tail 全 unit 证明
   \[
   \sum_{u<v<w}\Lambda_{uvw}>0
   \quad(N\ge3,z\ge N+2).
   \]
   \(N\ge9\) 是一张 94 项、总次数 13、最小系数 \(5/2\) 的普通正系数
   证书；\(N=3,\ldots,8\) 是六行覆盖全部 slack 的严格 Newton 证书，
   89,089 张原始 faces 全部交叉一致。另
   `root_intrinsic_third_face_global_unit_aggregate.md` 已参数闭合“只有一个
   nonunit 且它位于 root-neighbour endpoint”的任意 depth 族：inactive
   base 为 142 项 bulk 加六行全-slack 证书；有限 depth 修正为一张 281 项
   bulk 与七张低 residual 证书。更进一步，只要
   \(s=z-N-2\ge1\)，四个位置类型 \(\delta=1,2,3,\ge4\) 和任意 nonunit
   depth 全部严格满足 \(G=6T_3>0\)：\(q\ge8\) 的 base/step 分别为
   98/655 项正系数证书，低 residual 有 8 组 base/113 项 step，低 rank
   由 99 条全-slack Newton 行闭合。最后的 Catalan 顶层 \(s=0\) 三个
   internal 类型也已由
   `root_intrinsic_third_face_one_nonunit_catalan_proof.md` 严格闭合。
   正确递推必须保留 endpoint-inactive 共享 buffer：令
   \(V_\delta=U_\delta+B_0\)、\(D_d=(q+1)_d\)、
   \(R_d=(d+2q-7)_{d-1}\)，总量符号等于
   \(J_d=D_dM_\delta+R_dV_\delta\)。\(q\ge8\) 由三张 14 项 base、
   三张 120 项任意 depth step 和逐因子 ratio cap
   \((q+1)(q+2)\) 闭合；\(0\le q\le7\) 由 24 张 15 项 step 与
   \(10(q+1)\) cap 闭合；\(q=-1\) 有三张 13 项 inactive 证书。
   \(3\le N\le8\) 只剩 232 个真正有限低秩状态，原始整数最小值 5424。
   114,108 张原始 direct-\(K\) faces、534 个归一化、1,571 个
   product-ratio 和 2,613 个递推状态全部独立通过；独立审计见
   `root_intrinsic_third_face_one_nonunit_catalan_review.md`。因此 tail 恰有一个
   nonunit 时对任意 rank、path 长度、位置与 depth 均有 \(T_3>0\)；一般
   第三面的首个剩余域已严格推进到至少两个 nonunits。旧
   `root_intrinsic_third_face_one_nonunit_progress.md` 的 fixed-depth 结果
   仅保留为历史探索，不能再写成当前缺口。
7. **conditioned-star 的错误分块已被严格排除，新的 fixed-size 桥已建立。**
   `root_intrinsic_third_face_star_buffer_obstruction.md` 给出任意长族使
   \(S_1/2+S_2/3<0\)，并给出
   \(S_0+3S_1+2S_2=-124/7\) 的反例；所以必须保留第 4 点证明的
   \(S_0\ge0\) buffer。`root_intrinsic_third_face_star_fixed_size.md` 定义
   \[
   C_k=F_1+\frac{2k}{R-1}F_2
      +\frac{3k(k-1)}{(R-1)(R-2)}F_3,
   \]
   并严格证明 \(G\) 是这些自然 Bernstein controls 的正权混合。
   \(C_k\ge0\) 仍只是更强候选：\(z\le7\) 的 76,211 个 controls 无反例，
   不能当作参数证明；逐 retained subset 非负已有 \(-1/45\) 的严格反例。
8. **三种朴素 global depth 归纳和丢弃 \(F_1\) 都是假的。** 固定 \(N\)
   加深一个坐标、同步 \((d,N)\mapsto(d+1,N+1)\)、以及保持局部 residual
   的 \((d_i,d_j,N)\mapsto(d_i+1,d_j+1,N+2)\)，分别有精确负增量
   \(-10368,-840,-90552/5\)。另外
   \((F_1,F_2,F_3)=(6842/21,-1227/91,0)\)，所以不能先丢掉
   \(F_1\ge0\) 再证明 \(F_2+F_3\ge0\)。这些反例不否定 \(G\ge0\)，只否定
   错误的传播/分块工具。
9. **多 nonunit 的正确充分量。** 第 6 点已排除 \(h=0,1\)，所以只需处理 nonunit 数
   \(h\ge2\)。固定一个 nonunit hole \(w\)，令 \(A_w\) 是含 \(w\) 的
   单 unit faces 和、\(B_w\) 是含 \(w\) 的双 unit faces 和，并令
   \(J_w=5A_w+12B_w\)。精确双计数有
   \(\sum_wJ_w=2(5F_1+6F_2)\)，因此对 \(h>0\) 的一个真正充分局部目标是
   \[
   hJ_w+12F_3\ge0\quad\text{for every hole }w;
   \]
   求和即得 \(2hG\ge0\)。
   `root_intrinsic_third_face_mixed_per_nonunit_reduction.md` 已给出
   \(A_w,B_w\) 的 literal/pair-\(F\)/atom-path 三路精确式和 edge-moment
   接口；18,340 个恒等状态全部通过。该式在 \(z\le8\) 的 46,168 个精确
   \((word,w)\) 状态及 31,137 个随机状态中无反例，但仍只是候选。
   逐四点支付已被无穷族
   \[
   -\{K(w,x,u)+K(w,x,v)+K(w,u,v)\}
   =4506+5706\binom y1+910\binom y2+54\binom y3>0
   \]
   严格推翻。
10. **\(N=3\) 的完整第三面已经严格闭合。**
   `root_intrinsic_third_face_mixed_rank_three.md` 与
   `root_intrinsic_third_face_mixed_rank_three_h_three.md` 先闭合
   \(r\le1\)、\(h=1,2,3\) 和稀疏域；其中 \(h=2,3\) 的 capped-gap/Newton
   证书分别覆盖任意 path 长度，而不是 bounded-\(z\) 扫描。新的
   `root_intrinsic_third_face_mixed_rank_three_complete_proof.md` 一次闭合
   全部 \(h\ge4,r\ge2\)。核心是保留联合 unit moment
   \[
   W=T_{UU}+\frac34Q_{UUU},
   \]
   用 \(P_U\) 的 endpoint surplus 精确支付 \(W\) 的整个 \(b\)-负块，
   再以 \(e\le r-1,\ell_2\le r-2\) 和全部 depth 类的统一 \(L/S\) 下界
   得到显式六次多项式 \(\mathcal L(h,r)\)。三张普通正系数证书分别覆盖
   \(h\ge5,r\ge3\)、\(h=4,r\ge6\)、\(r=2,h\ge9\)，项数
   26/6/6、最小系数 6/78/30；只余八个 \((h,r)\) 对，精确化为 1,869 个
   真正有限 separated-minimum 状态，原始 \(K\) 最小值 170,304。故对每个
   rooted word 和每个 marked nonunit 都有
   \[
   N=3\Longrightarrow hJ_w+12F_3\ge0.
   \]
   对 \(w\) 求和给出 \(G\ge0\)，再由
   \(T_3=F_0+(F_1+G)/6\) 与已证 \(F_0,F_1\ge0\) 得到
   \[
   \boxed{N=3\Longrightarrow T_3\ge0}.
   \]
   因此第三面的第一个剩余 rank 已从 \(N=3\) 严格推进到 \(N\ge4\)；
   一般 \(N\ge4\) 和更高 intrinsic prefixes 仍缺。
11. **\(N=4\) 已建立完整截断/联合 moment 归约，并闭合一个无界 density cone。**
   `root_intrinsic_third_face_mixed_rank_four_sparse_proof.md` / `.py`
   独立核实：nonunit depths 恰分为 \(2,3,4,\ge5\)；相对 \(N=3\)
   新增的交叉 atoms 只有
   \(t_\beta(2,2)=(9,-3,1)\) 与
   \(q_\beta(2,1,1)=(27,-9,3,-1)\)，two-nonunit quadruple 仍严格截断。
   完整 per-nonunit 自由块唯一强制联合量
   \[
   W=T_{UU}+\frac38Q_{UUU},
   \]
   而 marked 修正还必须保留
   \(Q_{wUU}=-\binom r2+4M_1^{(w)}-16M_2^{(w)}+64M_3^{(w)}\)
   以及 depth-two nonunit-pair 的 \(\beta\)-histogram。同一 unit set 的两组
   精确 obstruction 分别给出 \(Q_{wUU}=-22,-6\)（目标差 774,144）和
   \(t_{wx}=-3,1\)（目标差 143,360），说明 global \(W\) 加一阶 hole
   数据不足；它们不是候选反例。另一方面，对 \(n\ge9\) 的三种 unit-count
   faces 作统一 atomwise 下界，写 \(r=1+x,h=8r+s\) 后得到一张 35 项、
   总次数 7、最小系数 15 的普通正系数证书，严格证明
   \[
   \boxed{N=4,\ r\ge1,\ h\ge8r\Longrightarrow hJ_w+12F_3>0}
   \]
   （\(r=0\) 取等号），path 长度和 depths 均不受限。默认核对 15,264 个
   截断/atom 状态、2,000 个原始分解、8,160 个 moment 恒等状态和 75,579
   个原始 faces。把同一粗下界限制到 \(h=7r\) 时最高项为
   \(-159744r^7\)，只否定该 atomwise 下界把阈值降到 7，不否定真实候选。
   一般 \(N=4\) 仍需联合 global \(W\)、marked star 与 depth-two pair
   histogram；不要退回逐固定 \(h\) 枚举。
12. **exactly-two-nonunit 已闭合三个 stable 类和三个 finite-only 类。**
   `root_intrinsic_third_face_two_nonunit_reduction.md` 用
   \((\delta_w,\delta_x,n_1,n_2)\) 把任意长 rooted cycle 的八组 atom
   counts 精确压成 38 个有向、24 个反射类；这是截断弧的完备分类，不是
   bounded-\(z\) 扫描。若两个 holes 恰为 root 的左右 neighbours，则
   descriptor 是 \((1,1,2,0)\)。在
   \[
   d,e\ge2,\qquad q=N-d-e\ge1,\qquad s=z-N-2\ge0
   \]
   上，完整 \(G\) 精确分成四个正 factorial factors 乘
   \((U,M_d,M_e,H)\)；平移后四张普通正系数证书分别有
   4,657/3,040/3,040/1,817 项，最小系数 15/9/9/45。factorial 归一化
   唯一漏掉的 \((d,e,q,s)=(2,2,1,0)\) 由原始式直接给出
   \(G=7{,}466{,}400>0\)。剩余 \(q\le0\) 又由
   `root_intrinsic_third_face_two_endpoint_nonpositive_residual_proof.md`
   严格闭合：精确分解
   \[
   G=U(N,s)+M(d,N-d,s)+M(e,N-e,s)+J(q),
   \]
   其中双 inactive base 恒有 \(U>0\)，两个单 endpoint 修正恒有
   \(M\ge0\)；\(q<0\) 时 \(J=0\)，而 \(q=0\) 时
   \[
   J=180(z-1)(z-2)(z-3)(N-2)>0.
   \]
   bulk/低 residual 共七张无界正系数证书，真正有限的小环只有 34 个状态，
   原始最小值 14,868。因此 descriptor \((1,1,2,0)\) 对任意 depths、rank
   与 slack 严格满足 \(G>0\)。另外
   `root_intrinsic_third_face_two_nonunit_finite_classes.md` 严格指出
   \((1,2,1,2),(2,2,1,2),(2,2,0,3)\) 三类满足 \(n_1+n_2=3\)，故只可能
   出现在 \(z=5,6\)；物理 rank 与 inactive depth 截断后共 52 个状态、
   358 张原始 faces，全部严格为正，最小 \(G=11{,}028\)。进一步，
   `root_intrinsic_third_face_two_nonunit_adjacent_endpoint_proof.md` 又把
   stable descriptor \((1,2,2,0)\) 对全部参数闭合。正确分块是
   \[
   G=\underbrace{(U_{\rm raw}+M_{2,{\rm raw}})}_{B>0}
     +M_{E,{\rm raw}}+H_{\rm raw};
   \]
   不能单独要求 distance-two mixed block 非负。\(v=N-e\ge8\) 由
   160 项 base、1,291 项任意 depth step 和 ratio cap
   \((v+1)(v+2)\) 闭合；\(0\le v\le7\) 有八张全-slack base、八张
   179 项 step 与 \(10(v+1)\) cap；\(N=3,\ldots,8\) 的 33 条 Newton
   行覆盖无界 slack。endpoint mixed 与 joint 块复用已证正证书，真正有限
   的 \(z=5,6\) 只有 34 个原始状态，最小 \(G=10{,}164\)。再进一步，
   `root_intrinsic_third_face_two_nonunit_separated_endpoint_proof.md` 闭合
   \((1,2,1,1)\)。这里正确分块升级为
   \(G=(U+M_2)+(M_E+H)=B+C\)：\(B\) 沿用上述递推，\(C\) 在
   \(q\ge5\) 用 811 项 base/4,823 项 step，在 \(q=1,\ldots,4\) 用
   caps 24/30/30/35 与四张 964 项 step；临界 \(q=0\) 由一条 bulk 和
   五条 fixed-depth rays 闭合。33+15 条低-rank Newton 行覆盖无界 slack，
   默认核对 6,141 个完整分块状态和 385 个 normalization；小环 25 态最小
   \(G=84{,}372\)。独立审计
   `root_intrinsic_third_face_two_nonunit_separated_endpoint_review.md` 又从原始
   four-block 重建 descriptor、\(G=B+C\)、全部 residual 分支和低秩
   Newton 行，结论为 PASS。因此 exactly-two-nonunit 当时只剩 18 个 stable
   reflection classes。随后
   `root_intrinsic_third_face_two_nonunit_distance_three_endpoint_proof.md`
   又闭合代数上最近的 \((1,3,1,1)\) 类（稳定代表 holes \((1,3)\)）。其
   endpoint mixed 与 joint 块和已证 \((1,2,1,1)\) 逐项完全相同，只需对
   新的 \(B=U+M_3\) 证明同型递推：bulk base/step 为 160/1,291 项，八条
   低 residual step 各 179 项，最小系数 15；33+15 条低秩全-slack
   Newton 行最小系数 5,400。默认 raw four-block/normalization 核对
   6,141/385 态，唯一小环 \(z=6\) 的 25 态最小 \(G=74{,}112\)。因此
   exactly-two-nonunit 当前还剩 17 个 stable reflection classes。
13. **更完整的 weighted tetrahedron 也已被无穷族推翻。**
   `root_intrinsic_third_face_weighted_tetrahedron_obstruction.md` 固定
   \(N=3\)、两个 depth-3 nonunits 与一条 internal unit edge，证明对
   \(z=20+y\)
   \[
   -W=91248+63900\binom y1+12216\binom y2+900\binom y3>0,
   \]
   其中
   \(W=5\{K(u,w,x)+K(v,w,x)\}+6\{K(u,v,w)+K(u,v,x)\}\)。未加权四面和的
   Newton 系数也严格为
   \((-2952,-8864,-1880,-144)\)。同步
   \((N,d,e)\mapsto(N+2,d+1,e+1)\) 传播另有
   \(-98546391366288\) 的正 residual 反例。所以下一步必须把 nonunit pair
   正资源、unit path 的二/三阶 moments 和 mixed quadruple 保持在更大的
   全局块中；不要退回逐四顶点、位置单调、individual Type-II 或 finite
   scan。一般 \(T_3\) 与完整 Tu--Deng 仍然开放。
14. **完整 \(N=4\) 第三面已经严格闭合，首个开放 rank 推进到 \(N\ge5\)。**
   在原交接后的连续推进中，
   `root_intrinsic_third_face_mixed_rank_four_density_three_proof.md` 先以
   global \(W=T_{UU}+3Q_{UUU}/8\) 和 path-moment caps 把 density cone
   从 \(h\ge8r\) 降到 \(h\ge3r\)；
   `root_intrinsic_third_face_mixed_rank_four_six_units_proof.md` 闭合
   \(2\le r\le6\)；
   `root_intrinsic_third_face_mixed_rank_four_thirty_holes_proof.md` 闭合
   \(h\ge30\)。最后的
   `root_intrinsic_third_face_mixed_rank_four_complete_proof.md` 按 endpoint
   unit 数 \(b=0,1,2\) 联合保留 singleton surplus 与 global moments，
   避免旧下界同时取两个不相容极值。条件 path caps 为
   \(e\le r-1,r-1,r-2\) 与
   \(M_2\le r-2,3r-6,6r-12\)；mixed star 用精确边矩
   \(\rho_y r+b+k_y\)，marked endpoint/internal quadruple 分别保留不同
   下界。由此此前唯一开放带
   \(r\ge7,2\le h\le29\) 化为 6,064 张六次严格 Newton 证书，全局最小
   系数 69,120，fingerprint 为
   `c28a8db5c29aeb80e7641acbf919e9b1504ed23531f1f8f701d2e649710cd293`。
   任意 mixed depths 由 homogeneous depth 分支的精确凸组合覆盖；不是
   uniform-depth 假设。唯一低边界 \((n,r,h)=(9,7,2),(10,8,2),(10,7,3)\)
   共 522 个 separated-minimum outer states，原始 full-\(K\) 最小值
   50,633,856。默认又核对 16,098 个 unit masks、346,368 个 mixed stars、
   86,592 个 marked stars、300 个原始 per-nonunit targets；独立审计结论
   PASS。因此严格得到
   \[
   \boxed{N=4\Longrightarrow T_3\ge0}.
   \]
   当前一般第三面的首个缺口已经从 \(N=4\) 推进到 \(N\ge5\)。这仍不证明
   一般 \(T_3\)，更不证明 \(T_4,\ldots,T_N\) 或完整 Tu--Deng 猜想。
15. **exactly-two-nonunit 已对任意 rank、slack、位置与 depths 完整闭合。**
   `root_intrinsic_third_face_two_nonunit_endpoint_batch_and_finite_proof.md`
   先补上两个 endpoint stable classes 与三个由 capped-arc 分类强制为单环的
   finite-only classes；随后
   `root_intrinsic_third_face_two_nonunit_nonendpoint_complete_proof.md`
   闭合最后 12 个无界 nonendpoint reflection classes。后者把原始 four-block
   精确重组为
   \[
   G=\left(\frac13U+M_w\right)
    +\left(\frac13U+M_x\right)
    +\left(\frac13U+H\right),
   \]
   并分别以 mixed/joint rising-product 递推证明三块严格为正。12 类每类
   71 张参数证书，连同 35 张 universal ratio 证书共 887 张；联合
   fingerprint 为
   `36e0e184e5d2093bdfd5fd2540f74c38d8e41892c5551ade13bdb6522f4317d4`。
   默认全量运行核对 6,639 个 literal raw states、29,520 个 component
   normalizations、20,640 个负 joint-residual 零块；唯一 \(z=6\) 边界
   的 25 态最小 \(G=150{,}852\)。与此前 12 类拼接后 24 个 reflection
   descriptors 全部覆盖，严格得到
   \[
   \boxed{\text{tail 恰有两个 nonunits}\Longrightarrow G>0}.
   \]
   所以一般第三面的首个剩余 nonunit 域已推进到至少三个 nonunits。
16. **完整 \(N=5\) 第三面已经严格闭合，首个开放 rank 推进到 \(N\ge6\)。**
   `root_intrinsic_third_face_mixed_rank_five_complete_proof.md` 保留唯一强制的
   \(W_5=T_{UU}+Q_{UUU}/4\)，以及 marked \(Q_{wUU}\)、pair
   \(t_{wx}\) 和新增的 \(Q_{wxU}\)。在 \(h\ge3,r\ge13\) 上，按 endpoint
   unit 数与 marked endpoint 类型得到五张 43 项、总次数 8 的二元 Newton
   证书，最小系数 15,120；\(2\le r\le12\) 的无界尾由 27 条全 \(h\)
   Newton rays 覆盖，之前唯一的 \(6\le n\le15\) 窗用逐坐标分离的精确
   minimum 闭合，共 411,285 个 outer states，最小值 4,646,592。
   \(h=2\) 不靠 bounded-length 扫描：30 个 stable descriptors、25 个 depth
   pairs、两个 markings 给出 1,500 条永久 gap rays；四个 finite-only
   descriptors 另有 200 态，最小值 8,238,528。全量脚本还核对 8,505 个
   truncation states、455,770 个 \(W_5\) masks、4,200 个原始 \(h=2\)
   states；完整 fingerprint 为
   `b20c8e825da9eca695a45361514c8c843150c3ac789b25d1f0611123ea21c4d4`。
   因而
   \[
   \boxed{N=5\Longrightarrow T_3\ge0}.
   \]
   与 \(N=3,4\) 拼接后，当前完整第三面的第一个开放 rank 是 \(N\ge6\)。
   一般 \(T_3\)、更高 intrinsic prefixes 与完整 Tu--Deng 仍未证明。
17. **一般 intrinsic 第三前缀已严格完整闭合。**
   `root_intrinsic_third_face_general_complete_proof.md` 将已证的
   \(N=3,4,5\)、\(h=0,1,2\)、\(r=0,1\) 与三个新参数分支无缝拼接。
   `root_intrinsic_third_face_general_endpoint_cones_proof.md` 闭合
   \(h\ge2N\) 的 high-hole 锥和 unit-dense 锥；
   `root_intrinsic_third_face_low_central_local_proof.md` 以 two-track
   rising-product 与 scaled Bernstein controls 证明 \(n\le2N\) 时每张
   all-unit / two-unit local face 严格为正；
   `root_intrinsic_third_face_general_central_proof.md` 再以独立 atom
   lower 和 105 个 scaled-simplex controls 闭合 \(n\ge2N+1\) 的
   central rectangle，并显式补上 \((N,r)=(7,15),(8,17)\) 两条 strip。
   最终对每个 marked nonunit 得到
   \(C_w=hJ_w+12F_3\ge0\)，再由
   \(\sum_wC_w=2hG\)、\(G=5F_1+6F_2+6F_3\) 与
   \(T_3=F_0+(F_1+G)/6\) 得到
   \[
   \boxed{N\ge3\Longrightarrow T_3\ge0}
   \]
   对任意 rooted word 和所有物理 depths 成立。
   `root_intrinsic_third_face_general_complete_proof.py` 的默认全量门禁
   重建 endpoint/central/low-central 与 \(N=3,4,5\) 的关键指纹，
   路由 991,742 个整数状态并命中全部 12 个分支；central 另有
   132,120 张 literal faces，最小 lower margin 为 57,679,776。
   两份独立审计
   `root_intrinsic_third_face_low_central_local_review.md` 与
   `root_intrinsic_third_face_general_complete_review.md` 均从第二实现重建
   controls、factorial normalization、分区与原始 kernels，结论为 PASS。
   因此 intrinsic 主线的下一关键层是 \(T_4\)，不再是任何
   fixed rank 或 multi-nonunit \(T_3\) 子域。完整 Tu--Deng 仍然开放。

## 2026-07-13：任意 short-gap 主线推进（root-anchor 已严格闭合 \(N\le4\)）

1. **“做到六短还是七短”没有有限终点。** 逐层排除 \(s=6,7,\ldots\)
   只有做到任意 \(s\) 才能证明完整猜想；当前严格的最小反例门槛仍是至少
   六个 short gaps。六点全集核虽已闭合，六短 proper residual 尚未闭合，
   所以不能宣称“至少七短”。本节的新主线绕过固定 \(s\)，直接寻找一个
   任意 path 长度的统一引理。
2. **完整 Clean 已精确归约到 root-anchor。** 对 ordinary subset contribution
   \(C_J\) 定义
   \[
   L_i=\sum_{J\ni i}\frac{C_J}{|J|}.
   \]
   严格恒等式 \(\sum_iL_i=\Delta_m\)。因此只要证明
   \[
   L_i\ge\mathbf1_{d_i\le m}
   \tag{RA}
   \]
   就立即得到 \(\Delta_m\ge s_m\)，进而证明完整 Tu--Deng。详见
   root_anchor_reduction.md。
3. **(RA) 已压成固定二状态正路径。** 令 \(N=m-d_i,n=z-1\)。统一共轭后
   \[
   L_i=[a^N]\int_0^1\frac{C_n(a,x)}{(1-a)(1-2a)}\,dx,
   \]
   \[
   U'=\frac{U-xa^dC}{1-a},\qquad
   C'=\frac{(1-2a)^2U+x(3-4a)a^dC}{1-a},
   \quad(U_0,C_0)=(1,-(3-4a)).
   \]
   等价 mixed matrix 为
   \(R_{d,x}=(1-x)R_\infty+xR_d\)，逐系数非负；唯一的 sign 已集中到
   terminal \(C\)。\(z\) 只体现为 path 长度。见
   root_anchor_integral_path.md。
4. **新的严格任意参数定理：root excess \(N\le4\) 全部闭合。**
   root_anchor_low_excess_proof.md 对 \(N=0,1,2\) 用 rooted-cycle
   pair/triple 计数证明 \(L_i\ge1\)。root_anchor_excess_three_proof.md
   再把 \(N=3\) 闭合：\(z\ge8\) 统一化为三个显式正多项式；
   \(z=5,6,7\) 的 5,376 个有限基例最小值为
   \(4,25/2,76/3\)。root_anchor_excess_four_progress.md 与
   root_anchor_excess_four_window_proof.md 又闭合 \(N=4\)。因此若所有
   active depths \(d_i\ge m-4\)，short gaps 可以任意多，Clean 已严格成立；
   当前 (RA) 真正剩余的是 \(N\ge5\)。
5. **\(N=4\) 的三段证明已经严密拼接。** \(z=6,7,8,9\) 的
   \(5^5+5^6+5^7+5^8=487500\) 个截断 words 由原始 rooted DP 穷尽；
   \(z\ge22\) 由 unit-edge Newton 展开和 mixed-depth charging 参数化证明，
   最弱参数下界在 \((z,r)=(22,20)\) 仍为 \(2597/15>1\)；
   \(10\le z\le21\) 由全整数 branch-and-bound 覆盖五字母
   \(\{1,2,3,4,I\}^{z-1}\)，共访问 1,913,487 个节点、剪枝 1,530,792 个，
   全部输出 `PROVED`。独立 Python 用原始 rooted DP 核对 96,875 个
   factor 恒等式。有限树只承担有限窗；无界 \(z\) 由参数证明承担。
6. **Intrinsic Bernstein 桥已经严格建立，第一面已对任意参数闭合。**
   把 root polynomial 写成本征 degree \(N\) 控制点
   \(\gamma_0,\ldots,\gamma_N\)，令
   \(T_k=\sum_{r=1}^k\gamma_r\)。root_intrinsic_prefix_bridge.md 用
   order-statistic 与 Abel 求和证明：若全部 \(T_k\ge0\)，则
   \((N+1)L_i\ge A_z(N)\)，从而推出 (RA)。
   root_intrinsic_first_face_proof.md 已对任意 \(N,z\) 和 depths 参数证明
   \[
   T_1=\gamma_1=A_z(N)+P_1/N>0.
   \]
   本节随后又闭合了 \(T_2\)，所以当前 intrinsic 主缺口从 \(T_3\) 开始；
   这是一条真正不依赖 short-gap 个数的统一路线。
7. **Intrinsic 第二面 \(T_2\) 已对任意 rank、任意 path 参数闭合。**
   root_intrinsic_second_face_N2_proof.md 对任意 cycle/depths 证明尖锐下界
   \[
   N=2\quad\Longrightarrow\quad T_2\ge5/2,
   \]
   不限制 short-gap 数。root_intrinsic_second_face_N3_proof.md 又把 112 个
   二点类型中的 111 个做成全 \(z\) Newton 正系数证书；唯一 internal-unit
   edge 型由非邻接 unit pairs 和 \(T_1\) buffer 支付，因而对任意参数证明
   \(N=3\Rightarrow T_2>0\)。
   root_intrinsic_second_face_N4_proof.md 再以 174 张全 \(z\) quartic
   Newton 证书和同型 unit-edge charging 证明 \(N=4\Rightarrow T_2>0\)。
   root_intrinsic_second_face_N5_proof.md 又重新生成 251 张全 \(z\) quintic
   证书并完成异常型支付，证明 \(N=5\Rightarrow T_2>0\)。
   更重要的是，一般 \(N\) 也已完成。root_intrinsic_second_face_reduction.md
   严格给出
   \(T_2=T_1+\sum_{u<v}\ell_{uv}\)，其中每个 \(\ell_{uv}\) 只依赖两个
   depths 和局部邻接签名；还参数证明了 edgeless 一阶资源
   \[
   A_z(N)-\frac1N\sum_{j=1}^{z-1}
   [a^{N-d_j}](1-a)^{-z}(1-2a)^3\ge0.
   \]
   可能为负的 local face 只出现在
   \(d_u=d_v=1,\beta(\{i,u,v\})=2\)。
   root_intrinsic_second_face_local_kernel.md 先用 fictitious nonadjacent
   kernel、三张 fixed-offset base 和一维 margin
   \[
   M_e=N(N+1)A_{N+1}-N^2A_N
   -(z-1)\{ND_{N-e+1}-(N-1)D_{N-e}\}>0
   \]
   参数闭合所有至少一个 depth 大于 1 的 faces；其中 \(M_e\) 有两份独立的
   任意参数递推证明：root_intrinsic_one_depth_monotonicity_proof.md 的
   28/67/131 项正系数证书，以及
   root_intrinsic_second_face_monotonicity_proof.md 的 rising-factorial
   Vandermonde 26/22/123 项证书。全部 unit-unit faces（不只负项）再压成
   \((r,h,e,c_2)\) 四个 path 图计数，root_intrinsic_unit_graph_proof.md
   参数证明 \(H+U>0\)。正确分块是
   \[
   T_2=T_1+U+\text{non-unit pairs}\ge H+U\ge0.
   \]
   因而统一 intrinsic 缺口已经严格从 \(T_2\) 推进到 \(T_3\)，不能再把
   \(T_2\) 写成 fixed-rank 或有限分类证据。
8. **第三面已有一个无界边界定理和两套精确归约，但一般 \(T_3\) 仍未闭合。**
   必须区分
   \[
   \gamma_3=T_3-T_2=P_0+3P_1/N+3P_2/\binom N2+P_3/\binom N3
   \]
   与 full-direct \(T_3\) 的 \((3,6,4,1)\) 权重。
   root_intrinsic_gamma3_tight_boundary_proof.md 已对任意
   \(N\ge3,z\ge N+2\) 参数证明 endpoint-inactive/internal-unit 族
   \((I,1,\ldots,1,I)\) 满足 \(\gamma_3>0\)：\(N\ge9\) 是 83 项严格
   正系数证书，\(3\le N\le8\) 是六行 Newton 正证书。另一方面，逐
   \(\gamma_3\)-simplex 非负严格为假；连续 internal \((2,1,2)\) 面的核满足
   \(K_{212}(z,N)=(8-3N)z^{N-1}/(N-3)!+O_N(z^{N-2})\)，故每个固定
   \(N\ge3\) 最终都为负。full-direct 侧已有严格恒等式
   \[
   K=\sum_{\{u,v\}}(N-2)\{3E_{uv}+4(z-1)(z-2)t_{uv}\}
     +3(z-1)(z-2)(z-3)q_{uvw},
   \]
   以及把所有含 unit 的 faces 按 unit 数等分的 conditioned quadratic
   \(V_u=\int_0^1S_u(x)\,dx\)。见
   root_intrinsic_third_face_direct.md。pair residual \(q=N-d-e\le0\) 的全部
   七种 \(F\) kernels 已由 second-face edgeless 定理与 \((1,2)\) 坐标传播
   参数闭合；\(q=0\) 最坏 \(\beta=2\) 仍留下严格系数 3，见
   root_intrinsic_third_face_pair_nonpositive_residual_proof.md。对 \(q\ge1\)，
   Type-I 双 depth 增量的 \(\beta=1,3\) 也已有两张 35 项 base 证书与一张
   29 项 adjacent 修正证书，见 root_intrinsic_third_face_pair_kernel_proof.md。
   root_intrinsic_third_face_pair_beta2_type_i_proof.md 又闭合最后的
   \(\beta=2\)：把 margin 精确拆成两个一坐标块，并分别参数证明
   \(H-8ZC_r>0\) 与 \(H+16Z(Z-1)H_{2,q}>0\)。两套任意长度
   rising-product 递推证书为 34/76/198 项和 64/76/262 项，最小系数均为
   1；默认又核对 395,010 个 fictitious 状态和 1,185,030 个全部真实
   signature 状态。因此 \(q\ge1\) 的 Type-I 已覆盖全部七种 ordered
   signatures。但 individual Type-II 已被同一 pair 文件严格推翻：真实
   signature \((2,1,1)\)、\(d=e=1\)、\(z=N+4\) 在
   \(q=N-d-e\ge67\) 形成无穷负族，首点 margin 为
   \[
   -1608206338476637218241970210184960712332900.
   \]
   因此不能再逐条证明 I/II；但真正的联合 buffer 已先闭合 all-unit 旧态：
   15 个 full signatures、3 个增量方向给出 45 张二元正系数证书，每张
   84 项、总次数 12、全局最小系数 3，从而任意 \(q\ge1,t\ge0\) 都有
   \[
   K(z,N+2;2,2,1)-K(z,N;1,1,1)>0
   \]
   及其坐标置换。剩余增量缺口是至少一个旧 depth 大于 1 的 I+II+II
   联合量。full-face 本体又有两个严格 nonunit 子域，见
   root_intrinsic_third_face_nonunit_face.md / .py：
   \[
   N\le d_{(1)}+d_{(2)}\Longrightarrow K\ge0
   \]
   由三个 \(q\le0\) pair kernels 立即推出，不限 unit 数；而
   \(r=N-\sum d_i\ge0\) 时，\((1,2,2)\) 的 45 张 154 项证书和
   \((2,2,2)\) 的 15 张
   174 项证书对全部物理 \(z\ge N+2\) 严格为正，最小系数分别为 3、9。
   depths \(\le6\) 的 3,000 张 all-\((r,s)\) 证书仍只是 finite-depth
   证据；任意 depth transition 与 \(-d_{\max}<r<0\) 中间窗未闭合。
   conditioned star 本身的 \(S_u(x)\ge0\) 仍存活，
   但“只查两个端点”的形状简化也已被严格推翻：
   \((z,N,u)=(21,3,3)\)、tail \(=(1,1,1,1,3,2^{13},3,2)\) 时顶点
   \(x_*=8168/119889\in(0,1)\)；该内点值仍严格为正，所以这不是 star
   正性的反例。两条纠错均见 root_intrinsic_third_face_direct.md。
   root_intrinsic_third_face_conditioning.md
   还严格证明 endpoint star 与 plain unit-star 都落在单个派生
   \(\beta_2\)，而非已证前缀 \(T_2=\beta_1+\beta_2\)；直接套用 \(T_2\)
   已由精确 obstruction 排除。
9. **Bernstein 前缀锥仍存活，但长程检查只是候选证据。** 若
   \[
   \Phi_i(x)=\sum_{k=0}^{n}b_k\binom nkx^k(1-x)^{n-k},
   \]
   则候选
   \[
   \sum_{j=0}^k b_j\ge k+1
   \]
   在 \(k=n\) 直接给出 (RA)。root_bernstein_prefix_search.c 用整数
   cardinality DP 精确检查 9,593,270 个 rooted words、2,034,717,922
   个前缀面，包括全部 \(\{1,\mathrm{inactive}\}\) words 到 \(z=20\)，
   均无反例；最小 margin 是真实等号 0。这是强有限证据，不是参数证明。
10. **两种过强局部化已被严格推翻。** marked/averaged cuts 在
   \((z,m)=(12,11)\)、\(d=(1^5,12^5,1^2)\) 上等于 \(-783\)。
   ordered root-facet 在
   \(z=14,m=13,d=(1^{11},14^3),i=5,k=11\) 上为
   \[
   G_{5,11}=-\frac{18434725}{42042},
   \]
   但聚合 root 仍有 \(L_5=19628335/77>1\)。同一例的末
   cardinality Bernstein 层为 \(-805233\)。所以不同 cuts/cardinality
   必须共享 buffer；不要再尝试逐 cut、逐 layer 非负。
11. **任意 \(s\) 的 diagonal simplex 恒等式已建立，但不是全证明。**
   tail-size \(t\) 的唯一对称权重为
   \[
   w_{s,t}=\frac1{(t+1)(s-1-t)}.
   \]
   固定 \(s\)、facet type、fixed depths 的 \(Z\to\infty\) 归一化极限已证
   严格为正；\(s=7,8\) 也有一批全 \(Z\) 证书。但粗 tail window 随
   \(s\) 线性增长，不能靠逐 \(s\) 有限证书收口。见
   general_s_diagonal_simplex.md。
12. **下一刀。** root-anchor 的低 excess 已推进完 \(N=4\)，下一统一层是
   \(N\ge5\)；intrinsic 侧的 \(T_1,T_2\) 已对任意 rank 闭合，当前第一缺口
   是 \(T_3\) 的三点 face 与 unit 边界聚合。当前两个最具体的参数目标是
   非 all-unit 三条 kernels 的 I+II+II 联合增量、nonunit 任意 depth transition 与
   中间负 residual 窗，以及 conditioned unit-star
   的真正 vertex/discriminant 或更弱积分不等式；不要再追 individual
   Type-II 或 endpoint-only star。\(\gamma_3\) 侧则需保留负
   \((2,1,2)\) faces 的共享 buffer。再往后仍需统一全部 \(T_k\)。
   完整 Tu--Deng 仍未证明；固定
   short-gap 路线的严格门槛仍只是“至少六短”，不能把 \(N\le4\) 特例、
   有限窗整数树或约 20 亿个有限 Bernstein 面误写成最终证明。

## 2026-07-13：六短 gap 首轮推进（全集核已闭合；proper residual 尚未闭合）

1. **六点全集核已有严格参数证明。** 对
   \(K_\beta=(1-2a)^{2\beta-2}(3-4a)^{6-\beta}\)，在 \(N\le z-7\)
   上已证明
   \[
   (-1)^{\beta+1}[a^N](1-a)^{-z}(1-2a)K_\beta
   +c_\beta A_{N+4}\ge0,
   \qquad(c_1,\ldots,c_6)=(2,2,2,1,1,1).
   \]
   `six_kernel_cert.py` 用五短同款的真正公共正分母与平移后非负系数
   证书完成 bulk；遗漏小 \(N\) 层是精确 \(q\)-多项式。独立整数回归
   67,824 个状态通过。细节：`six_kernel_bounds.md`。这只完成六短的
   full-set 项，不能单独推出六短 gap 排除。
2. **全坐标对角路线有精确四维 simplex 分解。** 六短 proper residual 的
   \(b\mapsto b+\mathbf1\) 差，先按子集大小均分到六个顶点；每个顶点再
   精确分成五个四维 facet。facet 内 tail-size \(t=0,\ldots,4\) 的权重为
   \[
   \frac1{(t+1)\binom{5-t}{4-t}}
   =(1/5,1/8,1/9,1/8,1/5).
   \]
   13 个合法 cyclic necklace 的 390 个带标号 facet 归为 17 类。
   `six_diagonal_explore.py` 已对深度 \(\{0,1,2\}^4\) 的 1,377 个
   facet 给出 all-\(z\) 正系数证书（最大秩 29，最小平移系数
   \(324728/45\)），并精确回归 subset→vertex→facet 恒等式。
3. **严格缺口不变。** 六短零坐标 proper residual 的五活跃点 charging，
   以及上述 17 类四维 facet 的无界 depth 尾部吸收，都尚未参数化证明。
   边界 buffer 和对角增量在 \(b_i\le2\) 的有限物理域回归无反例，但
   只能作为探索，不能宣称“至少七短 gap”。下一步应把五短的
   `one-dimensional → edge → facet → far tail` 分层吸收升到四维 facet，
   而不要把有限回归误写成定理。总进展：`six_short_progress.md`。

## 2026-07-13：五短 gap 已完整排除（严格门槛推进到六短 gap）

1. **严格全局结论已升级。** 五短 gap 的全集核与全部 proper-subset residual
   均已参数化闭合。因此任意最小前缀反例若存在，必须至少含**六个 short
   gaps**。完整 Tu--Deng 猜想仍未证明；下一主层是六短 gap。总证明见
   `five_short_complete_proof.md`。
2. **零坐标边界已经全部闭合。** 若五个 excess depth
   \(b=(b_0,\ldots,b_4)\) 中至少一个为零，则
   \[
   R_p(z,M,b)\ge c_\beta A_z(M+2),\qquad
   (c_1,\ldots,c_5)=(1,2,2,1,1).
   \]
   `five_support_four_residual.py` 把 30 个 proper subsets 分成 16 个 active
   交集块；14 个中间块由四个三顶点 facet 支付。五类 edge motif 只留下
   193 张全 \(z\) 证书，九类 facet 只留下 3,537 张全 \(z\) 证书；近端
   \(H(3)\) 再吸收 full-active 远端，剩余 17 型共 6,930 张全 \(z\) 证书。
   这些有限证书都来自严格统一尾界，不是 bounded-\(z\) 扫描。
3. **新的关键结构是全坐标对角单调性。** 在固定 \(z,M\) 且较高状态物理
   合法时，已证明
   \[
   R_p(z,M,b+\mathbf1)-R_p(z,M,b)\ge0,
   \qquad\mathbf1=(1,1,1,1,1).
   \]
   大小为 \(s\) 的 proper subset 在差值中精确乘
   \(1-a^{5-s}\)。把每项平均分给其所含顶点，再把每个顶点量分成四个三维
   facet，只剩 2 个一维型、5 个 edge 型、9 个 facet 型；分别由
   12、140、532 张全 \(z\) 证书和统一 Catalan 尾界闭合。详见
   `five_global_diagonal_monotonicity.py`。
4. **任意 \(b\) 从边界推出。** 令 \(r=\min_i b_i\)，从
   \(b-r\mathbf1\) 开始逐次加 \(\mathbf1\)。初态有零坐标，故由第 2 点
   非负；第 3 点保证每步不降，而 buffer \(c_\beta A_z(M+2)\) 与 \(b\)
   无关。于是五短 proper residual 对任意 \(b\) 成立。与
   `five_kernel_cert.py` 已证的五点全集核下界相加，buffer 完全抵消，五短
   gap 因而全部排除。
5. **独立回归全部通过。** 四活跃边界有 46,080 个原始 residual/16-block
   恒等式；对角增量有 75,816 个原始差/subset 压缩恒等式；另有 1,352 个
   boundary block--facet--edge 恒等式、768 个 subset--vertex--facet 恒等式、
   53,232 个 Pascal 状态和全集核 47,925
   个状态。既有 `five_gap_check` 独立有限行回归继续一致（有限回归不承担
   参数证明）。
6. **此前 boundary-first 反例仍然正确，但已被绕开。** 
   `five_boundary_classification.py` 的
   \(\Delta_I R_p=-22881\) 反例没有被撤销；错误的是试图证明一阶组合
   单调性。新证明保留绝对 residual buffer，并使用全坐标对角方向，所以不与
   该反例冲突。all-\(K\)-zero、support \(\le3\)、support \(\le4\) 的逐层文件
   `five_all_k_zero_residual_face.py`、`five_support_three_residual.py`、
   `five_support_four_residual.py` 可用于审计层级结构。
7. **下一步。** 优先参数化六点全集核常数，并测试五短证明中的 simplex
   charging / global-diagonal 分解能否升到六点。不要回到已证伪的五短
   boundary-first 单调路线。

## 2026-07-13：五短 boundary-first 候选被推翻，并完成全零补集面的参数分类

1. **五短边界的一阶二元组合单调性是假的。** 物理合法的显式反例为
   \[
   p=\texttt{triple\_single\_single},\quad I=(3,4),\quad
   b=(0,0,0,7,7),\quad (Z,z,M,q)=(17,18,-3,0),
   \]
   原始 proper residual 差、subset 压缩和双 motif 三路都给出
   \(\Delta_I R_p=-22881\)。更强地，`five_boundary_classification.py`
   对同一 \(b\) 证明每个 \(Z\ge17\) 都严格为负：清分母后
   \(-N(17+w)\) 的系数全部严格为正，最小系数 2048。此前“联合方向随机
   检查稳定”的观察是采样遗漏，不能再作为归约路线。
2. **反例不是孤立点，而有精确渐近机制。** 在三个 \(K\)-depth 全零时，
   边界量只有 3 个 shared 块、9 个 owned 块、18 个允许配对。九个 owned
   多项式全部精确因式分解为
   \[
   F_i(a)=(1-a)^3Q_i(a),\qquad Q_i\ge_{\rm coeff}0.
   \]
   第三个 shared 块满足 \(S_2'(1/2)=-1/4\)。允许族
   \((S_2,F_6,F_6)\)、对称 depth \(x=y=t\) 的归一化极限为
   \[
   -\frac14+\frac{t+1}{2^{t-1}},
   \]
   所以每个固定 \(t\ge6\) 在充分大 \(Z\) 上都给出负一阶增量。
3. **同一边界面的正半部已参数化证明。** shared 类型 0、1 的全部 15 个
   允许配对，对任意两个 \(I\)-depth、任意 \(Z,q\) 均非负。证明先用
   \((1-a)^3Q_i\) 丢弃 depth \(\ge2\) 的 owned 项，再把剩余压成 135 个
   真正有限的低层类型；每个清分母分子平移后系数非负，最小系数 64，
   小 \(Z\) 层精确处理，最后用 Pascal tail 推到任意 \(q\)。这不是有限
   depth 扫描。完整证明：`five_boundary_classification.md`；证书：
   `five_boundary_classification.py`。
4. **对主线的严格影响（历史状态，已由顶部新定理推进）。** 五短全集核定理、
   \(2+3\) 互补二阶定理、34 个全零 motif 基例都仍正确；失效的是“在边界
   证明 \(\Delta_I R_p\ge0\)，再由互补二阶推回内部”这一步。随后顶部新证明
   改用绝对 residual 的 simplex charging 与全坐标对角单调性，现已严格升级
   到六短 gap；但这个一阶组合单调性反例本身仍然有效。
5. **反例区的 all-K-zero connected-three proper residual 已全部闭合
   （现已被顶部任意 \(b\) 定理严格包含）。**
   三种允许配对 $(F_6,F_6),(F_6,F_7),(F_7,F_7)$，对任意两个 I-depth
   $x,y$、任意 $z,q$ 均已证明
   \[
   R_p-c_\beta A_z(M+2)\ge0.
   \]
   原始 30 项统一分成公共近端、两个 owned 中间块和一个远端块。近端至少
   为 $H(7)$；两个中间块均为 $(1-a)^3Q$、$Q\ge_{\rm coeff}0$；三个
   远端常数分别为 $143,142,323$。由
   $H(R)/H(7)\le R/(7\cdot2^{R-7})$ 统一处理大 $x+y$，剩余严格为
   $78+78+91=247$ 个小和类型；每个都有覆盖全部 $z$ 的正系数证书，最小
   系数 2272。Pascal tail 再提升到任意 $q$。详见
   `five_connected_residual_face.md` / `.py`（25,839 个原始/压缩状态和
   119,250 个 Pascal 状态独立通过）。这说明负增量否定的是归约工具，而非
   该整张困难边界面的 Tu--Deng 余量。

## 2026-07-13：五短 boundary-first 压缩与全零基例定理

1. **边界一阶量已精确压成两个四顶点 motif。** 固定二元方向
   (I\subset[5])、(K=I^c) 及 (k_0\in K,b_{k_0}=0)。含完整 (I) 的
   subset 在 Δ_I 中消失；提出公共 (1-a) 后，(K)-only subset 乘
   (1+a)，恰含一个 (I)-点的 subset 乘 (a)。全部 proper residual 精确
   写成 (L_{j_1}+L_{j_2})，其中每个 (L_j) 拥有含 (j) 的项并分得一半
   (K)-only 项。八类模式共产生 34 种带标号四顶点签名。原始 residual、
   subset 压缩、双 motif 三路恒等式见 `five_boundary_first.py`。
2. **(q) 已由 Pascal tail 严格消去。** 对任意固定签名和 depth，
   \[
   L_{Z+1}(q+1,b)=\sum_{h\ge0}L_Z(q+h,b).
   \]
   因此只要完成 (q=0) 层，全部 (q\ge0) 由 (Z)-归纳自动成立；剩余边界
   从“(q)+四个 depth”严格降为四 depth。
3. **全部 34 种全零 depth 基例已有全参数证明。** 当 (b=0) 时，
   (L_Z(0)=\sum_{r=1}^Rc_rH_Z(r))。使用
   \[
   H_Z(r)/H_Z(1)=
   \frac{r\prod_{i=2}^r(Z-i)}{\prod_{i=4}^{r+2}(2Z-i)}
   \]
   清除公共正分母；平移 (Z\mapsto Z+R+1) 后，34 个分子全部为非负系数
   多项式，最小系数为 24。小 (Z) 层精确为正，再用 Pascal tail 推到任意
   (q)。证书：`five_boundary_zero_certificate.py`；145,112 个独立递推状态
   通过。
4. **两个过强中间命题被严格排除。** 逐步 ratio/cap 锥会制造真实 Catalan 行
   不允许的 stopped-tail 伪反例；更重要的是，单个四顶点 motif 并非总非负。
   合法状态 `triple_single_single`, (I=(3,4)), (b=(0,0,0,30,0)),
   ((M,q,z)=(27,0,64)) 的两个 motif 分别约为
   (-6.35\cdot10^{32}) 与 (6.11\cdot10^{33})，配对总量仍正。因此后续证明
   必须保留两个 (I)-点对同一 (K)-side buffer 的动态共享。
5. **该节原定下一目标已作废。** 三个 (K)-depth 归零后的确只剩 3 种
   shared、9 种 owned、18 种合法配对，但配对总量并不总非负；顶部新节的
   无穷反例族已经严格否定 Pascal-tail surplus 目标。保留本节仅用于记录
   压缩恒等式和全零基例，不要据此启动单调归纳。

## 2026-07-13：五短 gap 首批全参数定理（全集核 + \(2+3\) 互补二阶）

1. **五点全集核已全部参数化证明。** 对
   \(K_\beta=(1-2a)^{2\beta-2}(3-4a)^{5-\beta}\)、
   \(A_n=[a^n](1-a)^{-z}(1-2a)\)，在 \(N\le z-6\) 上证明
   \[
   (-1)^{\beta+1}[a^N](1-a)^{-z}(1-2a)K_\beta
   +c_\beta A_{N+3}\ge0,
   \qquad(c_1,\ldots,c_5)=(1,2,2,1,1).
   \]
   `five_kernel_cert.py` 给出真正公共分母下的非负系数证书；bulk 最多 90 个
   分子项、11 个正分母因子，小 \(N\) 层是显式非负系数 \(q\)-多项式。
   `five_kernel_bounds.md` 记录完整证明。独立回归到 \(z=140\) 的 47,925 个
   状态，最小 margin 为 1；有限回归不承担证明作用。
2. **五短 proper residual 的 \(2+3\) 互补二阶已参数化证明。** 对任意
   二元方向 \(I\subset[5]\)、\(K=I^c\) 和全部合法参数，已有
   \[
   \Delta_K\Delta_I R_p(M,q,b)\ge0.
   \]
   四状态包含排除因子
   \((a^{|J\cap I|}-a^2)(a^{|J\cap K|}-a^3)\) 消掉含完整 \(I\) 或 \(K\)
   的 subset，只剩 5 个单点、9 个二点和 6 个三点；它们精确分解为六个
   三角 motif，且所有八类五点循环模式只产生七种签名。
3. **七种三角 motif 由 stopped-geometric 极射线严格闭合。** 令
   \(H_r=A^{(z-2)}_{z-3-r}\)、
   \(\delta_r=H_r-H_{r+1}\)。利用
   \(\delta_2=\delta_3\) 与
   \(\delta_{r+1}\le3\delta_r/4\)，把该系数锥的极射线写成有限
   \(3/4\)-geometric caps。每个局部单点支配二/三点原子的命题只需 56 个
   精确有理 cap 面；最后只剩七签名乘 \(3^3\) 个起点状态的 189 个资源分配。
   全分离签名 \((2,2,2,3)\) 恰好用尽抽象锥资源，其余均有余量。
4. **严格意义与后续纠错。** 这不是 fixed-\(b\) 证据，而是任意参数证明；
   它把“一阶量是否非负”的问题定位到
   \(\min_{k\in K}b_k=0\) 的四维边界。但顶部新节已经证明该边界一阶命题
   本身为假。因此互补二阶仍是有效结构定理，却不能再用于推出全局一阶组合
   单调性。本段当时的五短门槛现已由顶部 simplex/对角定理升级到六短；完整推导：
   `five_complementary_second_proof.md`；精确证书：
   `five_triangle_motif_proof.py`；原始 30 项/20 原子/6 motif 恒等式回归：
   `five_complementary_compression.py`（1,044,480 个状态，扫描最小值 95）。

## 2026-07-13：四短 gap 已严格排除（单非零边界全参数闭合）

1. **严格结论已升级。** 四短 gap 归约的最后缺口
   \(b=t e_i\) 已对任意 \(t\ge0\) 参数化证明。因此任意最小前缀反例若存在，
   现在必须至少含**五个短 gap**。这仍不是完整 Tu--Deng 证明。
2. **单非零余量压缩成三近端、八远端。** 对 \(t\ge1\) 令
   \[
   q=z-M-t-4,\qquad r=q+1,\qquad u=r+t,\qquad
   H_z(s)=A^{(z)}_{z-1-s}.
   \]
   每个模式、每个活动坐标的 margin 精确等于一个 \(H_z(r+\cdot)\) 近端块
   加一个 \(H_z(u+\cdot)\) 远端块；全部 16 个坐标状态按对称性只剩三种近端、
   八种远端。
3. **bulk 用尖锐 first-difference 吸收。** 令
   \(\delta_s=H_z(s)-H_z(s+1)\)。既有
   \(\delta_1=0,\delta_2=\delta_3\) 和
   \(\delta_{s+1}\le3\delta_s/4\ (s\ge3)\)。三种近端在 \(r\ge3\)
   都至少提供 \(3\delta_r\)；八种远端在 \(u\ge3\) 都不低于
   \(-4\delta_u\)，其中与最弱边界近端配对的两型有更强的
   \(-3\delta_u\) 界。因 \(u\ge r+1\)，最坏情形恰为
   \(3\delta_r-4\delta_u\ge0\)。
4. **两个 Euler/Catalan 异常层也严格闭合。** \(r=2\) 时近端按类型至少为
   \(3\delta_2\) 或 \(7\delta_2\)，与相应的
   \(-3\delta_u/-4\delta_u\) 远端配对；\(r=1\) 时近端统一至少
   \(7\delta_2\)，唯一的 \(u=2\) 远端统一至少
   \(-5\delta_2\)。因此没有遗漏 \(q=0,1\) 边界。
5. **证书是任意参数证明，不是有限扫描。** 每个远端都显式写成
   \[
   f(u)+c\delta_u=B\delta_u+
   \sum_jE_j\left(\frac34\delta_{u+j}-\delta_{u+j+1}\right),
   \qquad B,E_j\ge0.
   \]
   完整表和推导见 `single_nonzero_boundary_proof.md`。脚本
   `single_nonzero_boundary_proof.py` 生成全部有理证书，并用原始
   `residual_full` 对 \(z\le32\) 的 79,296 个合法状态逐项核对压缩恒等式。
6. **四短 gap 路线现已闭环。** 结合既有五类四点核下界、全零边界证书、
   pattern-independent 的 `complementary_second_proof.md` 和
   `boundary_motif_direct_proof.md` 的七型 motif 非负性，全部五种模式的二元
   组合单调性均已参数化证明。四短 gap 总前缀差值至少为 \(4\)。
   本段是四短闭环时的历史状态；顶部新节随后完成全部五短 proper residual，
   现已可严格宣称“至少六个短 gap”。

## 2026-07-10：path/polymer cap-compression 纠错与 Euler 修复

1. **固定常数 cap-compression 已被严格排除。** 旧候选
   $6F_r(U_{\rm lo})\ge F_r(U_{\rm hi})$ 在小范围通过，但 length 40、rank 20
   的 low/high words
   $(2,1^{39})$ 与 $(2,1^{19},2,1^{19})$ 给出
   $F_{20}(U_{\rm lo})=488671834579$、
   $F_{20}(U_{\rm hi})=3033837639612$，故 margin 为
   $-101806632138$。更一般的 rank $R$ 族有精确公式
   $$
   F_R(U_{\rm lo})=\frac{4^{R+1}+6R-13}{9},\qquad
   F_R(U_{\rm hi})=\frac{(12R+58)4^{R-1}+12R-28}{27},
   $$
   比值渐近 $R/4+29/24$，所以任何固定常数都不可能完成逐 cap 归约。
2. **新的 rank-dependent 候选通过大范围验证。** 当前候选是
   $(r+1)F_r(U_{\rm lo})\ge F_r(U_{\rm hi})$；已全量通过 length $\le6$、
   alphabet $\{1,2,3\}$ 的 length 9、随机 length $\le100$，并对上述解析族
   验证到 $R=80$。它仍是候选，不是证明。
3. **Euler tail suffix 稳定性已经严格证明。** 令 $\mathscr EF=(aF)'$，在压缩点
   定义 $X=\mathscr E(A_2U_{\rm lo})-A_2U_{\rm hi}$、
   $Y=\mathscr E(A_2V_{\rm lo})-A_2V_{\rm hi}$、$H=A_2V_{\rm lo}$，正确尾面为
   $$
   \mathcal E_t=X+\sum_{j=1}^t(4a)^j(Y+jH).
   $$
   depth 1 suffix 使 $\mathcal E_t'=\mathcal E_{t+1}$；depth $e\ge2$ 时有正分解
   $$
   \mathcal E_t'=X+\sum_{j=0}^t(4a)^j\left(
   \sum_{h=1}^{e-2}a^hX+a^{e-1}\mathcal E_1+4a^e(e+j-1)H\right)
   +D_{e,t}A_2U_{\rm lo},
   $$
   其中 $D_{e,t}=aG_e'+\sum_{j=1}^t(4a)^j(aP_e'+jP_e)$ 系数全非负。脚本已对
   1000 个随机状态精确核对传播恒等式。
4. **现在只剩新的局部 Euler 面。** 若 prefix 状态为
   $f_r=[a^r]A_2U,e_r=[a^r]A_2V$，压缩 depth 为 $d$，则目标精确化为
   $$
   [a^r]\mathcal E_t=r f_r+\sum_{j=0}^t4^j\left(
   r\sum_{h=1}^{d-1}f_{r-j-h}-f_{r-j-d}
   +4(r+1)e_{r-j-d}-4e_{r-j-d-1}\right)\ge0.
   $$
   已检查 prefix length $\le4,t\le10$ 的 2,741,838 个局部面全通过。下一步应
   参数化证明此式，而不是继续研究已证伪的 fixed-six 锥。代码：
   `cap_compression_cone.py`；完整推导：
   `2026-07-07-10am_path_polymer_smoothing_note.tex`。

## 2026-07-10：\(z=5,6\) 手工证明与 padding 审计

1. **已手工证明 \(z=5\)。** 新文件 `low_prefix_m4_z5.md` 证明
   \(\Delta_4\ge s_4\)，结合既有 \(m\le3\) Clean 定理，推出恰有五个零位时
   Tu--Deng 成立。四阶展开在 \(C_5\) 上只有两类负 motif：非相邻二点
   （每个 \(-1\)）与 edge-plus-isolated 三点（每个 \(-3\)）；单点余量通过
   \(P\le2n_2+n_1\)、\(3Q\le3n_0+3n_1\) 完全吸收。复现：
   `python3 low_prefix_m4_z5_check.py`，全 \(5^5=3125\) 个截断 gap 向量精确通过。
2. **已继续手工证明 \(z=6\)。** `low_prefix_m5_z6.md` 证明
   \(\Delta_5\ge s_5\)。\(C_6\) 完整展开只有四类负 motif，权重为
   \(-1,-3,-4,-9\)；单点余量
   \(13n_0+13n_1+8n_2+3n_3\) 通过 incidence bounds 和六个 \(U>0\)
   计数行吸收它们。`python3 low_prefix_m5_z6_check.py` 对全部
   \(6^6=46656\) 个截断向量逐项核对局部表、charging inequality 和
   \(\Delta_5\ge s_5\)。
3. **该简单 charging 在 \(z=7\) 精确停止。** 全零 gap 时单点余量为
   \(287\)，但负的三/四/五连块总量为 \(343\)，短缺 \(56\)；实际
   \(\Delta_6-s_6=4025\)，说明下一步必须保留正的多点项并做 run-level
   owned/shared 配对。复现：`python3 low_prefix_z7_obstruction.py`。
4. **旧 \(4\times\) padding 递推是假的。** 反例
   \(\mathbf g=(3,1,3)\)：\(\Delta_2(\mathbf g)=1\)，但
   \(\Delta_3(\mathbf g+(0))=3<4\)。`core_pd_verify.c` 与
   `pd_verify_fast.c` 曾把 \(2\times2\) 单位矩阵误初始化为仅左上角为 1，漏掉第二
   carry state；现已修正。详见 `padding_recursion_audit.md`。不能再用该递推由
   \(z=4\) 归纳到更大 \(z\)。

本目录目标是尝试证明 Tu-Deng 猜想：

\[
|S_t|\le 2^{k-1},
\]

其中

\[
S_t=\{(x,y)\in\{0,\ldots,2^k-2\}^2:
x+y\equiv t\pmod {2^k-1},\ w(x)+w(y)\le k-1\}.
\]

截至目前仍未完成完整证明。阶段性推导在
`tu_deng_carry_progress.tex`，核心检查代码在 `gap_prefix_check.py`、
`bernstein_prefix_check.py`、`short_gap_analysis.py`、`four_gap_explore.py`、
`four_gap_check.c`、`five_gap_check.c`、`prefix_domination.c`、`tudeng_verify.c`。
三点核下界的代数证明记录在 `kernel_bounds.md`，三短 gap 余量下界的证明记录在
`residual_bounds.md`，四点核下界记录在 `four_kernel_bounds.md`，四短 gap 余量
攻关记录在 `four_gap_residual.md`。文献路线对照见 `literature_review.md`；
Cheng/Cusick 新方法移植设想见 `cheng_strategy.md`。
**Chen--Lin--Wei 2020 桥接 + 前缀支配扩展记录在 `clw_bridge_note.md`。**

## 2026-07-10 路线 C 最新突破（互补二阶已参数化证明）

> 本节保留 2026-07-10 的历史状态；其中“单非零边界仍缺”的表述已被
> 2026-07-13 顶部新结论取代。

1. **完整 Tu--Deng 证明仍未完成，严格全局结论暂未升级。** hard patterns 的
   二元组合单调性已经完成参数化证明，但四短 gap 余量的单非零边界
   $b=t e_i$ 仍缺任意 $t$ 的参数证明，所以仍不能宣称“四短 gap 已排除”或
   “最小反例至少五个短 gap”。
2. **互补二阶子目标已经严格完成。** 新增 `complementary_second_proof.md`，对
   `two_pairs`、`four_block`、任意二元方向 $I$ 和全部合法 $M,q,b$ 证明尖锐下界
   \[
   \Delta_{I^c}\Delta_I R_p(M,q,b)\ge16.
   \]
   四状态包含排除因子
   \[
   (a^{|J\cap I|}-a^2)(a^{|J\cap I^c|}-a^2)
   \]
   消掉所有三点、四点误差项，只剩四个单点和 $K_{2,2}$ 的四条跨边。令
   $Z=z-2$、$H_Z(r)=A^{(Z)}_{Z-1-r}$，把每个单点的一半分给相接的两条跨边；
   每条边由 $H_Z$ 的整数递减性贡献至少 $4$，相加得到 $16$。等号在
   $b=0,M=-2,q=0,z=6$ 达到。
3. **大范围独立回归通过。** 已运行
   ```text
   python3 complementary_second_two_point.py --bmax 5 --Mextra 10 --qmax 10 --Zmax 120
   ```
   检查 32,310,642 个局部边状态和 1,881,792 个原始残差状态；压缩恒等式逐值
   一致，局部/全局最小值为 $4/16$。有限检查只作回归，结论本身已有参数证明。
4. **边界一阶量先压缩为六种三顶点 motif，随后已直接证明非负。** 新增
   `boundary_first_motif.py`。在 $\min_{j\in I^c}b_j=0$ 上，一阶增量精确拆成
   两个三顶点 motif；诱导邻接只有六类。出现五个稳定的联合单调性候选：$Z$
   单增，或 $Z$ 分别与 $q,b_j,b_k$ 同增，以及 $(Z,b_j,b_k)$ 同增。有限精确
   扫描均通过。扩大命令
   `python3 boundary_first_motif.py --bmax 5 --Mextra 8 --qmax 8 --mono-max 20 --mono-slack 20`
   已检查 384900 个原始边界状态和 5834430 个联合单调差分，全部通过。
   `boundary_motif_direct_proof.md` 进一步绕过五个候选：令
   $\delta_r=H_Z(r)-H_Z(r+1)$，用
   $\delta_1=0,\delta_2=\delta_3\ge\delta_4\ge\cdots$ 和
   $\delta_{r+1}\le3\delta_r/4$，把 owned 近端的 $\delta_s$ buffer 吸收四种
   远端核的 $-\delta_s$，并把 shared 两型直接写成非负 $\delta$ 和。因此六型
   motif 全部非负。互补二阶在非物理代数中间态仍有弱下界 $G_I\ge0$，所以
   可从任意 $b$ 降到 motif 边界；由此任意二元组合单调性 $\Delta_I R_p\ge0$
   已严格完成。
5. **最新文件。** `complementary_second_proof.md`（严格证明）、
   `complementary_second_two_point.py`（二点压缩回归）、
   `boundary_first_motif.py`（边界一阶 motif 分解）、
   `boundary_motif_direct_proof.md`（六型直接证明）、
   `boundary_motif_direct_check.py`（$\delta$ 恒等式回归）。

## 2026-07-04 路线 C 最新续探快照（四短 gap 组合单调性）

1. **完整证明仍未完成，严格结论不变。** 目前仍只能严格宣称：任意最小前缀
反例必须至少有四个短 gap；四短 gap residual buffer 还没有完整参数化证明，
不能宣称“四短 gap 已排除”或“最小反例至少五个短 gap”。

2. **一阶二元组合增量 fixed-\(b\) 证书扩展到 `bmax=5`。**
`increment_symbolic.py` 继续使用公共参数
\[
z=M+q+\sum_i(b_i+\mathbf 1_{\{i\in I\}})+4
\]
在同一公共正分母下证明 fixed-\(b\) 的二元组合增量
\[
\Delta_I R_p(b)=R_p(M,b+\mathbf 1_I)-R_p(M,b)\ge0.
\]
已运行
```text
python3 increment_symbolic.py --bmax 5 --quiet
```
two\_pairs 和 four\_block 每类各 7776 个 fixed-\(b\) 二元增量证书全通过，
最大 275 个分子项、21 个公共分母因子、60306 个小 \(M\) 边界。注意这仍是
有限 fixed-\(b\) 证据，不是任意 \(b\) 参数化证明。

3. **新增 `routeC_increment_templates.py`，抽出二元增量模板。**
该脚本把 hard patterns 的 \(\Delta_I R_p\) 写成不依赖固定 \(b\) 的有限模板：
对补集 \(C=[4]\setminus J\)，每项是
\[
\Delta^{|I\cap C|}\Phi_{p,C}\!\left(M+\sum_{i\in C}b_i+|C|-1\right),
\]
其中 \(\Phi_{p,C}\in\{A,T,-S,U_1,U_2\}\)，并进一步展开为
\[
D_n=A_{n+1}-A_n
\]
的线性组合。脚本已用 `residual_full` 对 \(z\le9,\ 0\le b_i\le3\) 做精确
self-check。该模板排除了两条省力路线：
   - 单非零边界 \(b=t e_i\) 一般不随 \(t\) 单调，不能降到 \(t=0\)；
   - 仅用三短证明中的粗事实 \(D_n\ge0\) 且 \(D_n\) 非降不足以证明组合单调性。
     在 \(b=0\) 已失败，two\_pairs 的典型尾和为 \(-30\)，four\_block 的典型尾和
     为 \(-14\)。后续必须使用 \(A_n\) 闭式或更强差分锥。

4. **新增互补二阶组合单调性候选。** `second_increment_symbolic.py` 研究
\[
\Delta_J\Delta_I R_p(b)
=R_p(b+\mathbf 1_I+\mathbf 1_J)-R_p(b+\mathbf 1_I)-R_p(b+\mathbf 1_J)+R_p(b).
\]
重叠二阶方向是假的，在 \(q=0\) 远区有明确反例，例如 two\_pairs:
\[
I=(0,2),\quad J=(0,3),\quad b=(0,0,4,4),\quad (M,z)=(0,16),
\]
给出 \(\Delta_J\Delta_I R_p(b)=-9117<0\)。另有
\[
I=(0,2),\quad J=(1,2),\quad b=(0,0,3,0),\quad (M,z)=(38,49)
\]
给出巨大负值。因此不能尝试“所有二阶方向非负”。

5. **稳定的新候选是互补二阶方向。** 对任意二元方向 \(I\subset[4]\)，令
\(I^c=[4]\setminus I\)，候选命题为
\[
\Delta_{I^c}\Delta_I R_p(b)\ge0
\]
（\(p=\) two\_pairs 或 four\_block）。已运行
```text
python3 second_increment_symbolic.py --bmax 4 --quiet
```
two\_pairs 和 four\_block 每类各 3750 个 fixed-\(b\) 互补二阶增量证书全通过，
最大 189 个分子项、17 个公共分母因子、24624 个小 \(M\) 边界。该性质若能
参数化证明，可把一阶组合单调性 \(\Delta_I R_p\ge0\) 降到三维边界
\[
\min_{j\in I^c} b_j=0.
\]

6. **新增三维边界一阶证书。** `increment_boundary_symbolic.py` 专门检查上述
互补二阶降维后的边界族：
\[
\min_{j\in I^c}b_j=0,\qquad \Delta_I R_p(b)\ge0.
\]
已运行
```text
python3 increment_boundary_symbolic.py --bmax 5 --quiet
python3 increment_boundary_symbolic.py --patterns two_pairs --bmax 6 --quiet
python3 increment_boundary_symbolic.py --patterns four_block --bmax 6 --quiet
```
全部通过。`bmax=5` 时 two\_pairs / four\_block 每类各 2376 个边界 fixed-\(b\)
一阶增量证书；`bmax=6` 时每类各 3822 个边界证书，最大 299 个分子项、
每个 fixed-\(b\) 最多 14 个小 \(M\) 边界。小范围数值定位显示这些边界族
的最小值倾向出现在 \(q=0,z=5\) 的极小边界，但这仍只是探索现象。

7. **互补二阶的 \(b=0\) 压缩核已单独证明。** 新增
`compressed_second_kernel.py`。当 \(b=0\) 时，互补二阶增量
\(\Delta_{I^c}\Delta_I R_p\) 压缩成四类 \(D\)-线性核（\(D_n=A_{n+1}-A_n\)）：
\[
\begin{aligned}
K_{\rm TP,end}&=16D_{M-1}-32D_M+20D_{M+1}-8D_{M+2}+4D_{M+4},\\
K_{\rm TP,mid}&=8D_{M-1}-8D_M-4D_{M+1}+4D_{M+4},\\
K_{\rm FB,end}&=12D_{M-1}-20D_M+8D_{M+1}-4D_{M+2}+4D_{M+4},\\
K_{\rm FB,cross}&=4D_{M-1}+4D_M-16D_{M+1}+4D_{M+2}+4D_{M+4}.
\end{aligned}
\]
这里 top 参数为 \(z=M+q+8\)。压缩 \(A\)-form 从 \(M\ge-5,\ q\ge0,\ z\ge5\)
就有意义；但作为真实 \(b=0\) 互补二阶残差比较，四个 residual 状态同时合法需要
\(M\ge-2\)。`compressed_second_kernel.py` 证明的是更宽的 \(M\ge-5\) A-form
范围。已运行
```text
python3 compressed_second_kernel.py
```
四个压缩核均通过正系数 bulk + 五个小 \(M\) 边界证书，最大 35 个分子项、
6 个公共分母因子。

8. **第三阶单坐标单调性路线被排除。** 一个自然想法是令
\[
G_I(b)=\Delta_{I^c}\Delta_I R_p(b)
\]
并证明 \(G_I\) 对每个单独 \(b_j\) 非降，从而把互补二阶降到 \(b=0\) 压缩核。
这是假的。新增 `third_increment_counterexample.py` 复现反例：
\[
p=\text{two\_pairs},\quad I=(0,1),\quad j=0,\quad b=(0,0,0,0),\quad
(M,q,z)=(-4,0,5),
\]
在公共 top 参数下
\[
G_I(b+e_0)-G_I(b)=-5<0.
\]
因此后续若要参数化证明互补二阶，必须把 \(b=0\) 压缩核与额外的小边界修正项
一起处理，不能只靠第三阶单调性。

9. **互补二阶最小值数值定位。** 新增 `second_increment_min_scan.py`（探索用，
非证明）。小范围命令
```text
python3 second_increment_min_scan.py --bmax 2 --Mmax 12 --qmax 5
```
显示 two\_pairs / four\_block 的所有二元方向最小值均为 \(16\)，出现在
\[
b=(0,0,0,0),\quad M=-2,\quad q=0,\quad z=6.
\]
较大范围 \(0\le b_i\le5,\ M<30,\ q<12\) 的手动扫描也给出同一最小点。
这提示互补二阶候选可能有更强下界 \(G_I(b)\ge16\)，但目前只是数值现象。

10. **互补二阶关于 \(q\) 的单调性有 fixed-\(b\) 证据。** 新增
`second_q_increment_symbolic.py`，在公共 top 参数
\[
z=M+q+\sum_i(b_i+1)+4
\]
下检查
\[
G_I(M,q+1,b)-G_I(M,q,b)\ge0.
\]
其中 \(q+1\) 项需要用
\[
\frac{F_{C+1}}{F_C}=\frac{2M+q+C-1}{M+q+C}
\]
换回同一个公共基底，因此多一个正分母因子 \(M+q+C\)。已运行
```text
python3 second_q_increment_symbolic.py --bmax 3 --quiet
python3 second_q_increment_symbolic.py --patterns two_pairs --bmax 4 --quiet
python3 second_q_increment_symbolic.py --patterns four_block --bmax 4 --quiet
python3 -u second_q_increment_slices.py --patterns two_pairs --directions 0,1 --bmax 5
python3 -u second_q_increment_slices.py --patterns two_pairs --directions 0,2 0,3 1,2 1,3 2,3 --bmax 5
python3 -u second_q_increment_slices.py --patterns four_block --bmax 5
```
全部通过。`bmax=5` 通过新增 `second_q_increment_slices.py` 按 pattern/direction
切片完成；two\_pairs 和 four\_block 各 6 个二元方向，每个方向 1296 个 fixed-\(b\)
\(q\)-增量证书，最大 274 个分子项、21 个公共分母因子、10051 个小 \(M\) 边界。
如果该性质能参数化证明，互补二阶强下界可进一步降到 \(q=0\) 层。

11. **互补二阶 \(q=0\) 层强下界有 fixed-\(b\) 证据。** 新增
`second_q0_layer_symbolic.py`，专门处理
\[
G_I(M,0,b)=\Delta_{I^c}\Delta_I R_p(b)
\]
的 \(q=0\) 层。脚本先在公共基底
\[
F_C(M)=\binom{2M+C-2}{M}/(M+C-1)
\]
下证明 bulk 区域 \(M\ge0\) 的
\[
G_I(M+1,0,b)-G_I(M,0,b)\ge0
\]
清分母分子为非负系数多项式，再精确检查有限个合法负 \(M\) 边界，从而对每个
fixed-\(b\) 证明
\[
G_I(M,0,b)\ge16.
\]
已运行
```text
python3 second_q0_layer_symbolic.py --bmax 1 --self-check --quiet
python3 second_q0_layer_symbolic.py --bmax 5 --quiet
python3 second_q0_layer_symbolic.py --bmax 5 --check-bmonotone --quiet
```
全部通过。`bmax=5` 时 two\_pairs / four\_block 每类各 7776 个 fixed-\(b\)
\(q=0\) 强下界证书，最小边界值为 \(16\)，最大 23 个分子项、22 个公共分母因子、
60306 个有限负 \(M\) 检查。`--check-bmonotone` 到 `bmax=5` 还显示在 \(q=0\)
合法共同 \(M\) 域内，\(G_I(M,0,b+e_j)-G_I(M,0,b)\ge0\) 的 fixed-\(b\) 坐标单调
证书也全部通过，有限负 \(M\) 检查数为 301530。结合第 10 点的 \(q\)-单调性
`bmax=5` 切片验证，当前合并结论是 \(0\le b_i\le5\) 时，已有 \(q\)-单调性 +
\(q=0\) 层下界给出互补二阶 fixed-\(b\) 强下界 \(G_I\ge16\)。

12. **互补二阶 \(q=0\) 层出现 \(b\)-高阶差分全正证据。** 新增
`second_q0_bdiff_symbolic.py`，对 ordered coordinates \((j_1,\ldots,j_r)\)
检查
\[
\Delta_{j_r}\cdots\Delta_{j_1}G_I(M,0,b)\ge0.
\]
重复坐标也允许，例如 \((0,0)\) 对应
\[
G_I(b+2e_0)-2G_I(b+e_0)+G_I(b).
\]
已运行
```text
python3 second_q0_bdiff_symbolic.py --order 2 --bmax 1 --quiet
python3 second_q0_bdiff_symbolic.py --order 2 --bmax 2 --quiet
python3 second_q0_bdiff_symbolic.py --order 2 --bmax 3 --quiet
python3 second_q0_bdiff_symbolic.py --order 3 --bmax 1 --quiet
```
全部通过。二阶差分到 `bmax=3` 时，two\_pairs / four\_block 每类各 24576 个
fixed-\(b\) 二阶 \(b\)-差分证书，最大 19 个分子项、18 个公共分母因子、
132288 个有限负 \(M\) 检查；三阶差分到 `bmax=1` 时每类各 6144 个证书。
所有 bulk numerator 都是原始非负系数，无需平移。这提示 \(q=0\) 层可能存在
全正差分/超模结构，可作为参数化证明 \(G_I(M,0,b)\ge16\) 的入口。

13. **当前最清晰的路线 C 子目标。** 将原先“证明任意四维一阶组合单调性”
拆成两个更小的参数化目标：
   - 证明互补二阶组合单调性
     \[
     \Delta_{I^c}\Delta_I R_p(b)\ge0;
     \]
   - 在边界 \(\min_{j\in I^c}b_j=0\) 上证明一阶增量
     \[
     \Delta_I R_p(b)\ge0.
     \]
若两步完成，则可参数化证明 two\_pairs / four\_block 的组合单调性，并把四短
余量最小值进一步降到更小的边界族。当前仍只有 fixed-\(b\) 符号证据，尚非
完整手工/参数化证明。

14. **相关新增/更新文件。**
   - `routeC_increment_templates.py`：二元组合增量模板与粗 \(D\) 锥诊断。
   - `second_increment_symbolic.py`：互补二阶组合增量 fixed-\(b\) 证书。
   - `increment_boundary_symbolic.py`：互补二阶降维后的三维边界一阶证书。
   - `compressed_second_kernel.py`：\(b=0\) 互补二阶压缩核证书。
   - `third_increment_counterexample.py`：第三阶单坐标单调性反例。
   - `second_increment_min_scan.py`：互补二阶最小值数值定位。
   - `second_q_increment_symbolic.py`：互补二阶关于 \(q\) 的 fixed-\(b\) 单调性证书。
   - `second_q_increment_slices.py`：互补二阶 \(q\)-单调性按方向切片长程验证。
   - `second_q0_layer_symbolic.py`：互补二阶 \(q=0\) 层 \(G_I\ge16\) 强下界证书。
   - `second_q0_bdiff_symbolic.py`：互补二阶 \(q=0\) 层 \(b\)-高阶差分证书。
   - `four_gap_residual.md`：已记录上述路线 C 续探细节和复现命令。
   - `路线.md`：已同步路线 C 状态和关键文件索引。


## 2026-07-04 路线 C 续探快照（CLW 桥接）

1. **完整证明仍未完成。** 但本轮产出了一个独立的阶段性成果：**把
Chen--Lin--Wei 2020 的 $w(t)\le10$ 结果从两个方向加强**——(a) 不等式从
Tu-Deng 升级为更强的**前缀支配**（对所有 $m<z$）；(b) 极值表从 $n\le10$
扩展到 $n\le18$，并给出极值结构的解析刻画。
详见 `clw_bridge_note.md`。

2. **扩展极值表（Section 3）。** 利用 CLW 的 deficit 递推
$\operatorname{deficit}_{k+1}=2\operatorname{deficit}_k+1$（CLW Lemma 7
当 $\operatorname{len}(t)+w(t)<k+1$ 时），极值 $t$ 的渐近比由
$1-(\operatorname{deficit}_{k_0}+1)/2^{k_0-1}$ 决定。通过对全部 $2^{n-1}$
个有序合成搜索，重现了 CLW Table I 的 $n=3,\ldots,10$（hex 全匹配），
并扩展到 $n=11,\ldots,18$。复现脚本：`extremal_contiguous.py`。
结果表：`extremal_table_extended.md`。

3. **极值核心的结构刻画（Section 4）。** 观察到极值核心（非零 gap 部分）
是 $n$ 的**平衡合成**：分 $m=\lfloor\sqrt{n-1}\rfloor+1$ 部分，每部分为
$\lfloor n/m\rfloor$ 或 $\lceil n/m\rceil$。这把极值搜索从 $2^{n-1}$ 降到
$O(\sqrt n)$ 个候选。公式对 $n=2,\ldots,18$ 全部验证通过。

4. **前缀支配对全部 CLW 归约基例成立（Section 5）。** 枚举了
$w(t)\le9$ 的全部 CLW 归约基例（322 875 个，仅 $w(t)=9$ 一类），
验证：(a) Tu-Deng 成立；(b) **前缀支配**（对所有 $0\le m<z$）成立。
$w(t)=10,11$ 的验证仍在跑（`pd_verify_parallel.py`）。

5. **零填充保持前缀支配（Section 6）。** 对每个归约基例添加
$1,\ldots,6$ 个零 gap 后仍满足前缀支配。对 $w(t)\le9$ 全部验证。
结合 CLW 的归约定理，这推出：**前缀支配（蕴含 Tu-Deng）对所有
$w(t)\le9$ 的 $t$、对所有 $k$ 成立**——比 CLW 的 Tu-Deng-only 更强。

6. **五短 gap 屏障推到 $z\le45$（Section 7）。** `five_gap_check --zmax 45`
全量通过，全局最小值 $5$，无反例（此前为 $z\le25$）。$z\le60$ 正在跑。
任意最小前缀反例若存在，在 $z\le45$ 范围内必须至少有六个短 gap。

7. **CLW Table I 的 $n=2$ 条目疑为笔误。** CLW 报告 $.9$，但我们的精确
计算和 $n=3,\ldots,10$ 的全匹配模式表明 $n=2$ 应为 $.C$。

8. **产出文件索引。**
   - `clw_bridge_note.md`：本轮研究 note（主文档）。
   - `extremal_contiguous.py`：极值搜索（有序合成）。
   - `extremal_table_extended.md`：扩展极值表 $n=2,\ldots,18$。
   - `pd_verify_parallel.py`：并行前缀支配验证器。
   - `pd_verify_reduced.py`：串行版（含逐 padding 检查）。
   - `pd_parallel_11.log`：$w(t)\le9$ 验证日志。
   - `pad_preservation_8_10.log`：$w(t)=8$ 的 padding 保持验证日志。


## 2026-07-04 补充快照

1. **完整证明仍未完成，严格结论未变。** 目前仍只能严格宣称：任意最小前缀
反例必须至少有四个短 gap；四短 gap 余量还没有完整手工证明，不能宣称
“最小反例至少五个短 gap”。
2. **新增 path/polymer 结构路线。** 新建研究记录
`2026-07-07-10am_path_polymer_smoothing_note.tex`（文件名前缀按用户要求保留）。
该 note 不覆盖原有稿件，记录了把 rank-one 误差集合按 open path interval
polymers 重组的尝试。令
\[
\rho=(1-2a)^2,\qquad \tau=3-4a,\qquad d_i=g_i+1,
\]
open path 分区函数满足
\[
H_i=a^{d_i}(Z_{i-2}+\tau H_{i-1}),\qquad
Z_i=Z_{i-1}-\rho H_i,
\]
并令
\[
B_i:=Z_{i-2}+\tau H_{i-1}.
\]
于是
\[
1-Z_n=\sum_{i=1}^n \rho a^{d_i}B_i.
\]
3. **推翻了一个过强的裸 path surplus 引理。** 原先猜测
\[
\Lambda_{z,m}(1-Z_n)\ge \#\{i:d_i\le m\}
\]
对任意 open path 成立，其中
\[
\Lambda_{z,m}(P)=[a^m]\frac{(1-a)^{-z}}{1-2a}P(a).
\]
该命题是假的：\(z=3,m=2,d=(1,2,1)\) 时
\[
Z_3=1-2a+8a^2+O(a^3),\qquad
\Lambda_{3,2}(1-Z_3)=2,
\]
但三个位置均满足 \(d_i\le m\)。失败原因是 open path 断环后丢掉了首尾相接的
cyclic run；这不是 Tu-Deng 路线本身的反例。
4. **新的候选核心引理：open-state smoothing。** 当前最有希望替代四短 gap
case analysis 的结构命题是
\[
[a^N](1-a)^{-z}(1-2a)B_i(a)\ge1,
\qquad 1\le i\le z-1,\quad 0\le N\le z-2.
\]
若该命题成立，则对长度 \(n\le z-1\) 的 open path 可推出每个 short depth
至少贡献 \(1\) 的 surplus；循环情形还需补上 wrap-around correction。
这个路线解释了四短 gap barrier：障碍很可能来自按点集 \(J\) 展开而非按连续 run
和状态 \(B_i\) 展开。下一步应寻找对
\[
B_i=(1+(3-4a)a^{d_{i-1}})B_{i-1}-(1-2a)^2a^{d_{i-2}}B_{i-2}
\]
不变的多层 coefficient cone，可能同时涉及
\([a^N]A_{z-r}(a)B_i(a)\) 的若干层。
5. **文献目录更新。** `literature/` 新增五篇有效 PDF：
`On a Conjecture of Cusick Concerning the Sum of Digits of n and n+t.pdf`
（27 页）、
`A lower bound for Cusick's conjecture on the digits of n+t .pdf`
（9 页）、
`About the Tu-Deng Conjecture for w(t) Less Than or Equal to 10 2020-227.pdf`
（6 页）、
`A structural decomposition of the correlation measure.pdf`（31 页）和
`On a Conjecture about Binary Strings Distribution.pdf`（1 页）。前两篇应作为
Cusick/Cheng 路线背景优先阅读；第三篇是 Chen--Lin--Wei 关于 `w(t)<=10` 的
Tu-Deng 特殊情形，应补入文献边界；`A structural decomposition...` 很可能与
Sobolewski--Spiegelhofer 分量/相关测度结构路线相关，应和 rank-one/run-polymer
展开对照阅读；`On a Conjecture about Binary Strings Distribution.pdf` 虽为有效 PDF，
但仅 1 页，需确认是否为完整论文。此前明显无效下载曾隔离到
`literature/invalid_downloads_2026-07-04/`，用户已要求删除，该目录现已删除。

## 2026-07-03 最新快照

1. **完整证明仍未完成。** 当前主命题仍是 gap 前缀支配：
\[
\operatorname{Pref}_m(R_{\mathbf g})
\le
\sum_{r=0}^m2^{m-r}\binom{z+r-1}{r},
\qquad 0\le m<z.
\]
取 \(m=z-1\) 即推出 Tu-Deng。
2. **严格证明进度**：已证明任意最小前缀反例必须至少有四个短 gap
（即 \(g_i<m\) 的位置至少四个）。两短 gap 和三短 gap 已完整排除；
三短证明由 `kernel_bounds.md` + `residual_bounds.md` 给出。
3. **四短 gap 状态**：四点全集核下界五个模式已全部证明：
\[
W_0\ge -A_{N+2},\quad W_1\ge -2A_{N+2},\quad
W_2\ge -2A_{N+2},\quad W_3\ge -2A_{N+2},\quad W_4\ge -A_{N+2}.
\]
四短余量下界还没有完全手工证明。`four_gap_residual.md` 记录了当前最强进展：
isolated 余量已可证；one\_pair / triple\_single 有边界归约和部分证明；
two\_pairs / four\_block 发现了组合单调性，可把最小值降到单非零边界族，
但任意参数的完整证明仍未完成。2026-07-03 补充：`residual_symbolic.py`
已修正正偏移项清分母因子错误；修正后可对五类全零边界，以及五类所有
单非零固定边界 \(b=t e_i,\ 0\le t\le5\) 给出全 \(z,M\) 符号证书。
`fast_combined_mono.py` 中四短枚举的多余第五重循环也已修正；修正后
two\_pairs / four\_block 的二元组合单调性到 \(z\le11\) 仍全量通过。
2026-07-03 再补充：`residual_symbolic.py` 的固定小 \(M\) 边界函数
`A_fixed_index_numer` 已修正一元展开偏移错误，正确使用
\[
\binom{z+n-2}{n}=\frac{(z-1)z\cdots(z+n-2)}{n!}.
\]
修正后 `python3 residual_symbolic.py` 仍全部通过。新增/重写
`increment_symbolic.py`，统一公共参数
\[
z=M+q+\sum_i(b_i+\mathbf 1_{\{i\in I\}})+4
\]
后在同一公共正分母下证明固定 \(b\) 的二元组合增量非负。已运行
`python3 increment_symbolic.py --bmax 4 --quiet`：two\_pairs 和 four\_block
每类 3750 个固定增量证书全通过，覆盖所有二元方向、所有
\(0\le b_i\le4\)、全合法 \(z,M\)。这仍是有限 fixed-\(b\) 符号证据，
不是任意 \(b\) 参数化证明。
4. **计算证据**：`./four_gap_check --zmax 61` 全量通过，五类四短模式最小总差值
均为 \(4\)，最小点为 \((z,m,d_1,d_2,d_3,d_4)=(5,1,1,1,1,1)\)。
`five_gap_check.c` 对五短 gap 全量验证到 `five_gap_z25.log` 中的 \(z\le25\)，
全局最小值为 \(5\)。`five_gap_z30.log` 目前只记录到 \(z=29\)，不要把它当作
完整 \(z\le30\) 结论。
5. **低阶前缀精确公式**：已补充 \(m=1,2,3\) 的闭式公式。令
\(\Delta_m=\operatorname{RHS}_{z,m}-\operatorname{Pref}_m(R_{\mathbf g})\)，
则
\[
\Delta_1=\#\{i:g_i=0\},
\]
且当 \(z\ge3\) 时，若
\[
n_0=\#\{i:g_i=0\},\quad n_1=\#\{i:g_i=1\},\quad
e_0=\#\{i:g_i=g_{i+1}=0\},
\]
则
\[
\Delta_2=(z-2)n_0+n_1-\binom{n_0}{2}+4e_0.
\]
此前前缀支配和严格等号条件已对 \(m=1,2\) 完全证明。2026-07-03 补充：
已完成 \(m=3\) 闭式。令
\[
n_j=\#\{i:g_i=j\},\quad
e_{00}=\#\{i:g_i=g_{i+1}=0\},\quad
e_{01}=\#\{i:\{g_i,g_{i+1}\}=\{0,1\}\},
\quad
c_{000}=\#\{i:g_i=g_{i+1}=g_{i+2}=0\},
\]
则当 \(z\ge4\) 时
\[
\Delta_3=
\frac{z(z-3)}2 n_0+(z-2)n_1+n_2
-(z-6)\binom{n_0}{2}-n_0n_1+4e_{01}
+4(z-n_0-2)e_{00}+\binom{n_0}{3}+16c_{000}.
\]
该式已在 `low_prefix_m3.md` 中证明非负，且等号当且仅当所有 \(g_i\ge3\)。
`low_prefix_formula_check.py` 已加入 \(m=3\) 复现检查。
**★ Clean 猜想 \(m\le3\) 已完整证明（2026-07-03 第四节，见
`clean_m23_theorem.md`）**：\(\Delta_m\ge s_m:=\#\{i:g_i<m\}\) 对 \(m=1,2,3\)
全部成立。\(m=2\) 用循环零位聚簇界 \(e_0\ge\max(0,2n_0-z)\) + 凹性证明，等号
\(\iff n_0=0\)；\(m=3\) 按 \(n_0\) 相对 \(z\) 分四区域，Region III 精确三次平移后
系数全非负、Region IV 精确分解 \(\frac{z(z-5)(z+14)}6\ge0\)、\(z=4\) 有限穷举。
这是 Clean 猜想（蕴含 Tu-Deng 前缀支配）首个非平凡已证片段。证书脚本：
`clean_m2_proof.py`、`clean_m3_regions.py`、`clean_m3_proof.py`、
`clean_m23_fast.py`、`delta3_formula_check.py`。
6. **全局验证**：原始 Tu-Deng 已由 `tudeng_verify.c` 系统验证到 \(k\le32\)；
前缀支配已由 `prefix_domination.c` 系统验证到 \(z\le10\)。
7. **文献结论**：不能宣称 carry/gap/block 思路全新。Flori 系列已经有 carries、
block variables、稀疏零位和 extremal isolated-zero family。当前可能的新意是
prefix-domination + rank-one expansion + short-gap kernel/residual hierarchy；
已读文献中未发现这条同型证明路线。
8. **新方向**：Kaimin Cheng 的 arXiv:2606.23398（2026-06-22）声称完全证明
Cusick 猜想，核心工具是 exact deconvolution、first-exit stopped random walk、
subsequence ideals、marked-deletion bijection。`cheng_strategy.md` 记录了把该方法
循环化移植到 Tu-Deng 的设想；这是 speculative，但值得优先试。
## 文献调研要点

详细对照见 `literature_review.md`。下一轮继续攻关前应先接受以下结论：

1. **carry/block 不是新想法。** Flori--Randriambololona--Cohen--Mesnager 2010
已经把 Tu-Deng 改写成 carries 问题，并研究 long block、asymptotic true、
以及 high number of 1s and isolated 0s 的 extremal family。
2. **Flori--Randriam 2012 是最接近当前路线的文献。** 它研究模 \(2^k-1\)
加法 carry 数，在 \(\min\alpha_i\ge B-1\) 的稀疏零位约束下证明
\(P_{t,k}\) 只依赖 \(\beta_i\)，并给出对称多项式/闭式表达和极限性质。
3. **但当前 prefix/kernel 机制未在已读文献中出现。** 已读全文中没有发现
归一化 gap 转移矩阵 \(M_g\)、所有 \(m<z\) 的前缀支配、
\(M_g=L+a^gE\) 的秩一误差展开、短 gap 最小反例分层、三点/四点 kernel
与 residual buffer 的同型证明。
4. **Cusick--Li--Stănică 2011、Cheng--Hong--Zhong 2015、Chen--Lin--Wei 2020**
主要是低 \(w(t)\) 或补元低 weight 的直接计数/有限化路线；它们和当前
固定 \(z=k-w(t)\)、按短 gap 排除反例的路线互补。
5. **Spiegelhofer--Wallner 2019** 证明几乎处处成立，方法是 moments、
recurrences、有理生成函数和 Chebyshev 集中；它不是逐个 \(t\) 的确定性
gap-prefix 不等式。
6. **Qarboua--Schrek--Fontaine 2016** 给出 mirror symmetry 与特殊族，
可作为对称性工具背景，但不是 prefix/kernel 路线。
## 当前最有价值的路线

使用循环进位模型。把 \(x,y,t\) 写成长度 \(k\) 的循环二进制串，引入
\[
c_i\in\{0,1\},\qquad x_i+y_i+c_{i-1}=t_i+2c_i .
\]
求和得到
\[
w(x)+w(y)=w(t)+|c|.
\]
令 \(z=k-w(t)\) 为 \(t\) 的零位数，则 Tu-Deng 条件等价于
\[
|c|\le z-1.
\]

逐位转移矩阵为
\[
A_0(u)=
\begin{pmatrix}
1&u\\
0&2u
\end{pmatrix},
\qquad
A_1(u)=
\begin{pmatrix}
2&0\\
1&u
\end{pmatrix}.
\]
于是
\[
|S_t|=\sum_{r=0}^{z-1}[u^r]\operatorname{tr}
\bigl(A_{t_0}(u)\cdots A_{t_{k-1}}(u)\bigr).
\]

## Gap 模型

按循环顺序列出 \(t\) 的零位。令 \(g_i\) 为第 \(i\) 个零位后连续的
1 的个数。令 \(a=u/2\)，
\[
M_g=
\begin{pmatrix}
1+a+\cdots+a^g&2a^{g+1}\\
2(a+\cdots+a^g)&4a^{g+1}
\end{pmatrix}.
\]
记
\[
R_{\mathbf g}(a)=\operatorname{tr}\prod_{i=1}^zM_{g_i}.
\]
Tu-Deng 可由如下前缀支配推出：
\[
\sum_{r=0}^m2^{-r}[a^r]R_{\mathbf g}(a)
\le
\sum_{r=0}^m2^{-r}[a^r](1-a)^{-z},
\qquad 0\le m<z.
\]
特别地，取 \(m=z-1\) 得到所需上界。

整数缩放形式：
\[
\operatorname{Pref}_m(R_{\mathbf g})
\le
\sum_{r=0}^m2^{m-r}\binom{z+r-1}{r},
\quad
\operatorname{Pref}_m(F)=\sum_{r=0}^m2^{m-r}[a^r]F.
\]

## 已证明和验证

1. 已证明 \(z\le3\)，即 \(w(t)\ge k-3\) 时 Tu-Deng 成立。
2. 补元对称性：
\[
d_r(t)=d_{k-r}(2^k-1-t).
\]
3. 原始剩余类代表下的平均进位重量为
\[
z-\frac{k}{2^k-1}.
\]
4. Lean 4 框架在 `TuDengFormal/`，当前验证了 gap 前缀支配
\(z\le5\)，以及原始 Tu-Deng \(k\le5\)。一般证明仍有两个
`sorry`：`prefix_domination_lemma_general` 和
`prefix_domination_implies_tu_deng`。
5. `prefix_domination.c` 对前缀支配做快速穷举，已用于检查
\(z\le10\) 全部 gap 向量无反例。\(z=9\) 时规范化循环类
43,046,889 个；\(z=10\) 时规范化循环类 1,000,010,044 个。所有
\(m<z\) 的最大值都达到 RHS。
6. `tudeng_verify.c` 对原始 Tu-Deng 做快速验证。`verify_31_32.log`
记录：
   - \(k=31\)：最大值达到 \(2^{30}\)，无违例。
   - \(k=32\)：最大值达到 \(2^{31}\)，无违例。

## 秩一展开

有
\[
M_g=L+a^gE,\qquad E=cr,
\]
其中
\[
L=
\begin{pmatrix}
\frac1{1-a}&0\\
\frac{2a}{1-a}&0
\end{pmatrix},
\qquad
E=
\binom{1}{2}
\begin{pmatrix}
-\frac a{1-a}&2a
\end{pmatrix}.
\]

进一步令
\[
A=\frac1{1-a},\quad
B=-\frac{a(1-2a)^2}{(1-a)^2},\quad
C=\frac{a(3-4a)}{1-a}.
\]
对误差集合 \(J\subseteq[z]\)，令
\[
\beta(J)=\#\{i:i\in J,\ i+1\notin J\}
\]
为空集和全集取 \(0\)。则
\[
R_{\mathbf g}(a)
=(1-a)^{-z}
+
\sum_{J\ne\varnothing}
(1-a)^{-z}
(-1)^{\beta(J)}
a^{\sum_{i\in J}(g_i+1)}
(1-2a)^{2\beta(J)}
(3-4a)^{|J|-\beta(J)}.
\]
全集项最低次数至少为 \(z\)，对目标前缀 \(m<z\) 无影响。

这个公式是当前最重要的结构：每个真正的误差连通分量贡献一个负号和
\((1-2a)^2\) 因子，提示应使用有限差分、全正性或带边界数的聚合物展开。

## Bernstein 形式

令
\[
\Delta_r=\binom{z+r-1}{r}-[a^r]R_{\mathbf g}(a).
\]
定义
\[
\mathcal B_{m,j}(\mathbf g)=
\sum_{r=0}^j2^{j-r}\binom{m-r}{j-r}\Delta_r,
\qquad 0\le j\le m<z.
\]
这是差值多项式
\[
D_m(x)=\sum_{r=0}^m\Delta_rx^r
\]
在区间 \([0,1/2]\) 的 Bernstein 系数的整数缩放。

关键等价性：
\[
\mathcal B_{m+1,j}=\mathcal B_{m,j}+2\mathcal B_{m,j-1},
\qquad
\mathcal B_{m,0}=0.
\]
因此所有 Bernstein 系数非负等价于所有对角项
\[
\mathcal B_{m,m}=\sum_{r=0}^m2^{m-r}\Delta_r\ge0,
\]
也就是原前缀支配。Bernstein 形式不是更强猜想，但它提供了有用的
bookkeeping 递推。

`bernstein_prefix_check.py` 已穷举验证 \(z\le7\)。由于 Bernstein
形式等价于前缀支配，`prefix_domination.c` 的结果同时给出
\(z\le10\) 的 Bernstein 系数非负。\(11\le z\le13\) 随机测试中未发现
反例。

## 新的组合计数形式

前缀泛函可写为
\[
\operatorname{Pref}_m(F)=[a^m]\frac{F(a)}{1-2a}.
\]
因此前缀差值是
\[
[a^m]\frac{(1-a)^{-z}-R_{\mathbf g}(a)}{1-2a}.
\]
从进位支撑模型还得到
\[
[a^r]R_{\mathbf g}(a)
=
\sum_{\substack{C\text{ 合法}\\ |C|=r}}
4^{Z(C)-h(C)}.
\]
于是前缀支配等价于
\[
\sum_{\substack{C\text{ 合法}\\ |C|\le m}}
2^{m-|C|}4^{Z(C)-h(C)}
\le
\sum_{r=0}^m2^{m-r}\binom{z+r-1}{r}.
\]
右端计数对象可解释为
\[
(n_1,\ldots,n_z,s,\epsilon),\qquad
n_i,s\ge0,\quad \sum_i n_i+s=m,\quad \epsilon\in\{0,1\}^s.
\]
所以新的纯组合目标是构造注入：
\[
(C,\text{内部零位的 }4\text{-标号},\text{slack 的 }2\text{-标号})
\hookrightarrow
\{(n_1,\ldots,n_z,s,\epsilon):\sum n_i+s=m\}.
\]

## 新的部分证明

已证明一个“两缺陷以内”情形：固定 \(m<z\)，若 gap 向量中至多两个
分量满足 \(g_i<m\)，则前缀支配成立。

单短 gap 的证明来自统一分母展开：唯一短 gap \(g<m\) 时，\(m\) 阶
以下唯一误差项是
\[
-(1-a)^{-z}a^{g+1}(1-2a)^2.
\]
前缀差值等于
\[
[a^{m-g-1}](1-a)^{-z}(1-2a)\ge0,
\]
因为令 \(n=m-g-1\)，有
\[
[a^n](1-a)^{-z}(1-2a)
=\binom{z+n-1}{n}-2\binom{z+n-2}{n-1}
\]
且 \(n=0\) 时系数为 \(1\)；\(n\ge1\) 时它等于
\[
\frac{z-n-1}{n}\binom{z+n-2}{n-1}\ge0
\]
（用 \(n\le m-1<z-1\)）。

两个短 gap 的证明令
\[
A_n=[a^n](1-a)^{-z}(1-2a).
\]
在 \(0\le n\le z-2\) 上 \(A_n\) 非负且非降。两个短 gap 不相邻时，
二点误差项由
\[
[a^N](1-a)^{-z}(1-2a)^3=A_N-4A_{N-1}+4A_{N-2}\le A_N
\]
控制；相邻时，由
\[
[a^N](1-a)^{-z}(1-2a)(3-4a)=3A_N-4A_{N-1}
\]
控制。单点误差项给出至少两个 \(A_N\) 量级的正贡献，因而总差值
非负。所以任何最小反例在对应的 \(m\) 下必须至少有三个 \(<m\) 的短 gap。

三短 gap 已进一步归约为三个有限差分不等式，并已完成证明。令
\[
A_n=[a^n](1-a)^{-z}(1-2a),\quad A_n=0\ (n<0),
\]
\[
S(n)=A_n-4A_{n-1}+4A_{n-2},\qquad
T(n)=3A_n-4A_{n-1}.
\]
若三个短 gap 的深度为 \(d_i=g_i+1\)，\(N=m-d_1-d_2-d_3\)，则：

- 三个孤立短 gap：
\[
\sum_i A_{m-d_i}-\sum_{i<j}S(m-d_i-d_j)
+U_0(N),
\]
其中
\[
U_0(n)=A_n-8A_{n-1}+24A_{n-2}-32A_{n-3}+16A_{n-4}.
\]
- 一个相邻对加一个孤立短 gap：
\[
\sum_i A_{m-d_i}+T(m-d_1-d_2)
-S(m-d_1-d_3)-S(m-d_2-d_3)+U_1(N),
\]
其中
\[
U_1(n)=-3A_n+16A_{n-1}-28A_{n-2}+16A_{n-3}.
\]
- 三个连续短 gap：
\[
\sum_i A_{m-d_i}+T(m-d_1-d_2)+T(m-d_2-d_3)
-S(m-d_1-d_3)+U_2(N),
\]
其中
\[
U_2(n)=9A_n-24A_{n-1}+16A_{n-2}.
\]

这些表达式先用 `short_gap_analysis.py --zmax 25` 验证到 \(z\le25\)
全部非负，最小值为 \(3\)，出现在
\((z,m,d_1,d_2,d_3)=(4,1,1,1,1)\) 的孤立型。随后通过
`kernel_bounds.md` 和 `residual_bounds.md` 完成通用证明；因此最小反例
必须至少有四个短 gap。

更细的充分分解如下。三点核已证明满足
\[
U_0(n)\ge -A_{n+1},\qquad
U_1(n)\ge -2A_{n+1},\qquad
U_2(n)\ge -A_{n+1}.
\]
证明记录在 `kernel_bounds.md`。核心是代入
\[
A_n=\frac{z-n-1}{z-1}\binom{z+n-2}{n}
\]
后化成正系数多项式；\(U_0\) 的边界 \(z=n+4\) 单独处理。
去掉三点核后，三类"单点项 + 二点项"余量满足
\[
\sum_i A_{m-d_i}-\sum_{i<j}S(m-d_i-d_j)\ge A_{N+1},
\]
\[
\sum_i A_{m-d_i}+T(m-d_1-d_2)-S(m-d_1-d_3)-S(m-d_2-d_3)
\ge 2A_{N+1},
\]
\[
\sum_i A_{m-d_i}+T(m-d_1-d_2)+T(m-d_2-d_3)-S(m-d_1-d_3)
\ge A_{N+1}.
\]
这三个余量下界已在 `residual_bounds.md` 中证明。核心换元为
\(M=N+1\)、\(b_i=d_i-1\)，并令 \(D_n=A_{n+1}-A_n\)。用
\(D_n\ge0\)、\(D_n\) 在 \(0\le n\le z-4\) 非降、
\[
S(n)\le D_n,\qquad T(n)\ge -A_{n+1},\qquad S(n+1)-S(n)\le D_{n+1}
\]
证明余量的单调降维：\(R_0\) 对三个 \(b_i\) 非降，\(R_1\) 对相邻
对两个 \(b_i\) 非降，\(R_2\) 对中间 \(b_i\) 非降。\(M<0\) 时右端
为 \(0\)，合法极小边界使相关 \(S\) 项消失；\(M\ge0\) 时降到边界后
由 \(S\le D\)、\(T\ge -A_{n+1}\) 吸收负项。

结合 `kernel_bounds.md`，恰有三个短 gap 的情形已排除。因此任意最小前缀
反例必须至少有四个短 gap。可用
`python3 short_gap_analysis.py --zmax 25 --check-bounds` 复现较小范围检查。

四短 gap 的探索脚本为 `four_gap_explore.py`。它使用统一子集公式
\[
(-1)^{\beta(J)+1}
[a^{m-\sum_{i\in J}d_i}]
A(a)(1-2a)^{2\beta(J)-2}(3-4a)^{|J|-\beta(J)}
\]
自动生成四短 gap 的五类相邻模式：孤立、一个相邻对、两个相邻对、三连块
加孤立、四连块。`python3 four_gap_explore.py --zmax 16 --self-check`
已通过；其中 `--self-check` 会先把同一公式在三短 gap 情形下与
`short_gap_analysis.py` 的三种表达式逐项比对。

更强的 C 版检查器为 `four_gap_check.c`。它同时检查：

- 四短总表达式非负；
- 四点核下界；
- 去掉四点核后的余量缓冲下界。

五类四点核 \(W_i\) 满足
\[
W_0\ge -A_{N+2},\quad W_1\ge -2A_{N+2},\quad
W_2\ge -2A_{N+2},\quad W_3\ge -2A_{N+2},\quad W_4\ge -A_{N+2}.
\]
这些核下界已由 `four_kernel_bounds.md` / `four_kernel_cert.py` 证明。
对应的余量目标为
\[
P_0\ge A_{N+2},\quad P_1\ge 2A_{N+2},\quad
P_2\ge 2A_{N+2},\quad P_3\ge 2A_{N+2},\quad P_4\ge A_{N+2}.
\]
`./four_gap_check --zmax 61` 已全量通过，最小总表达式仍为 \(4\)。
四短 gap 到 \(z\le61\) 无反例，最小值为 \(4\)，出现在
\((z,m,d_1,d_2,d_3,d_4)=(5,1,1,1,1,1)\)。

`four_gap_residual.md` 记录了四短余量的最新攻关：

- isolated 余量已通过正系数化完全证明；
- one\_pair、triple\_single 可降到部分边界族，边界族有符号/数值证据；
- two\_pairs、four\_block 的简单单变量单调性失败，但发现了组合单调性：
  在任意至少两个 \(b_i=d_i-1\) 同时增加的方向上非降。该发现可把最小值
  降到“至多一个 \(b_i>0\)”的参数化边界族；
- 这些边界族目前主要由 `residual_boundary.py`、`trivariate_check.py` 和
  `four_gap_check.c` 数值验证覆盖，还没有完整手工证明。

因此不能把“四短 gap 已完全排除”写成定理。严格结论仍是“最小反例至少四个短 gap”；
四短排除是下一步核心缺口。已排除的粗路线：把三点项全部替换为三点核粗下界太弱；
简单全方向单调性只适用于四孤立型，一个相邻对仅对该相邻对两个 \(b_i\) 单调，
三连块仅对中间点单调，两个相邻对和四连块没有这种简单单调降维。

五短 gap 的 C 检查器 `five_gap_check.c` 已验证到 `five_gap_z25.log` 中的
\(z\le25\)，所有八类五点相邻项链无反例，全局最小值为 \(5\)。该部分只是强计算证据，
尚未进入手工证明。

## 已排除路线

不要继续尝试逐 gap 单调或简单前缀锥不变性。反例：
\[
(g_0,\ldots,g_8)=(0,0,0,0,4,3,4,0,0).
\]
把 \(g_0=0\) 替换成 \(8\) 后，截断和下降：
\[
\Phi_9(R_{(0,0,0,0,4,3,4,0,0)})=\frac{30535}{128},
\]
\[
\Phi_9(R_{(8,0,0,0,4,3,4,0,0)})=\frac{30533}{128}.
\]
两者仍小于 \(2^8=256\)，所以这只排除局部单调策略，不反驳猜想。

另一个失败命题是 \(f_W=rM_{h_1}\cdots M_{h_n}c\) 的所有加权前缀非正。
它在 \(n=8\) 失败：
\[
(h_1,\ldots,h_8)=(0,0,0,4,3,4,0,0),
\qquad
\sum_{j=0}^{8}2^{-j}[a^j]f_W(a)=\frac1{64}>0.
\]

## 下一步

当前最具体的主攻点是证明对角前缀差值
\[
\mathcal B_{m,m}(\mathbf g)=
\sum_{r=0}^m2^{m-r}
\left(\binom{z+r-1}{r}-[a^r]R_{\mathbf g}(a)\right)\ge0.
\]
建议优先尝试上面的注入证明；这是目前最接近组合证明的形式。并行路线是
从统一分母展开入手，把非空 \(J\) 的贡献按循环边界数 \(\beta(J)\)、
大小 \(|J|\)、以及 gap 权重 \(\sum_{i\in J}g_i\) 分组，寻找有限差分
或 sign-reversing involution。

也可以尝试证明更一般的核非负性：对所有 \(m<z\)，
\[
\sum_{J\ne\varnothing}
(-1)^{\beta(J)}
[a^{\le m-\sum_{i\in J}(g_i+1)}]
(1-a)^{-z}(1-2a)^{2\beta(J)}(3-4a)^{|J|-\beta(J)}
\le0.
\]
这里全集项可忽略。
