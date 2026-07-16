# Tu--Deng 猜想 first-exit 证明与 Lean 形式化总结

## 1. 结论

本目录保存了《涂-邓猜想的首出与字典序边界证明》原始中文 TeX 以及完整的
Lean 4 形式化。最终得到：对任意自然数 `k,t`，若

\[
k\ge 2,\qquad 0<t<2^k-1,
\]

则

\[
\operatorname{tuDengCount}(k,t)\le 2^{k-1}.
\]

Lean 最终定理为：

```lean
theorem TuDeng.FirstExit.tu_deng_conjecture_full
    (k t : ℕ) (hk : 2 ≤ k) :
    TuDeng.TuDengConjecture k t
```

该定理在
[`FirstExitNat.lean`](lean/TuDengFormal/FirstExitNat.lean#L530) 中。

## 2. 目录内容

```text
final/
├── Tu_Deng_Conjecture_Proof_Revised_ZH.tex   # 原始中文证明
├── PROOF_SUMMARY.md                         # 本文件
└── lean/
    ├── lean-toolchain                      # Lean 4.32.0-rc1
    ├── lakefile.toml                       # Mathlib/Lake 配置
    ├── lake-manifest.json
    ├── TuDengFormal.lean                   # 完整证明的导入入口
    ├── AxiomAudit.lean                     # 公理依赖审计
    └── TuDengFormal/
        ├── TuDengDefinitions.lean          # 原猜想的定义
        ├── FirstExitCore.lean              # 字典序语言与标记删除
        ├── FirstExitBoundary.lean          # 定向边界递推
        ├── FirstExitPolynomial.lean        # 边界枚举多项式
        ├── FirstExitFunctional.lean        # 严格负半平面泛函
        ├── FirstExitCarry.lean             # 进位码、循环旋转与半界
        └── FirstExitNat.lean               # 原始模计数的精确双射
```

原始 TeX 的 SHA-256 为：

```text
e7a6013373033125e445a84a2e6c00c932bcd7cabf7d203fb3b3beb6378e9c63
```

`final/` 中的 TeX 与当前目录的原文是逐字节一致的。

## 3. 整体证明依赖链

```text
markedDelete_injective_on
        ↓
marked_deletion_inequality
        ↓
lex_language_halfplane_with_exception
        ↓
cross_boundary_identity
        ↓
cross_boundary_halfplane_bound
        ↓
cyclicNegativeCount_special_bound
        ↓  循环旋转
cyclicInputCount_bound_of_nonconstant
        ↓  原计数与进位计数的有限集双射
tuDengCount_eq_cyclicInputCount
        ↓
tuDengCount_bound
        ↓
tu_deng_conjecture_full
```

## 4. TeX 命题与 Lean 定理的对应

| TeX 中的阶段 | 数学作用 | 关键 Lean 定理 | Lean 文件 |
|---|---|---|---|
| 子序列理想与定向边界 | 定义首次离开主子序列理想的定向边界 | `boundary_true_iff`, `boundary_concat_same`, `boundary_concat_other` | [`FirstExitBoundary.lean`](lean/TuDengFormal/FirstExitBoundary.lean) |
| “边界递推” | 证明向目标词追加 0/1 后边界的精确不交分解 | `lexBoundary_concat_same`, `lexBoundary_one_concat_zero`, `lexBoundary_zero_concat_one` | [`FirstExitBoundary.lean`](lean/TuDengFormal/FirstExitBoundary.lean#L177) |
| “正系数边界差提升” | 将边界差写成非负系数多项式与异常单项式 | `positive_prefix_lift` | [`FirstExitPolynomial.lean`](lean/TuDengFormal/FirstExitPolynomial.lean#L375) |
| “交叉边界恒等式” | 证明 \(C_v=1+(X+Y-1)J_v+s_v\) | `boundary_tree_identity`, `cross_boundary_identity` | [`FirstExitPolynomial.lean`](lean/TuDengFormal/FirstExitPolynomial.lean#L324) |
| “商多项式的字典序模型” | 将 \(J_v\) 实现为显式字典序语言的枚举多项式 | `langFinset_eq`, `disjoint_subword_lexBoundary`, `enumerator_langFinset` | [`FirstExitPolynomial.lean`](lean/TuDengFormal/FirstExitPolynomial.lean#L467) |
| “删除一个 1 会降低字典序” | 证明字典序语言对删除 1 封闭 | `lex_delete_true`, `markedDelete_injective_on` | [`FirstExitCore.lean`](lean/TuDengFormal/FirstExitCore.lean#L95) |
| “带标记删除不等式” | 得到 \(b j(a,b)\le(a+b)j(a,b-1)\) | `marked_deletion_inequality` | [`FirstExitCore.lean`](lean/TuDengFormal/FirstExitCore.lean#L359) |
| “单边删除与半平面上界” | 使用标记删除支付严格负半平面质量及异常项 | `halfplaneDefect_le_half`, `lex_language_halfplane_with_exception`, `lex_language_halfplane_bound` | [`FirstExitCore.lean`](lean/TuDengFormal/FirstExitCore.lean#L457) |
| 对交叉边界施加半平面泛函 | 把多项式恒等式变成数值上界 | `phiNeg_Lambda_Jenum`, `phiNeg_Cenum_formula`, `cross_boundary_halfplane_bound` | [`FirstExitFunctional.lean`](lean/TuDengFormal/FirstExitFunctional.lean#L265) |
| “精确首出归约” | 证明活跃进位码与定向边界等价，并得到每个码的 \(2^{k-m}\) 重数 | `validCode_after_active`, `validCode_zero_start`, `validCode_one_start`, `codeMultiplicity_of_valid` | [`FirstExitCarry.lean`](lean/TuDengFormal/FirstExitCarry.lean#L54) |
| 特殊目标词 \(10v\) 的半界 | 把循环进位计数归一化为交叉边界的半平面质量 | `cyclicNegativeCount_special`, `phiNeg_Benum`, `cyclicNegativeCount_special_normalized`, `cyclicNegativeCount_special_bound` | [`FirstExitCarry.lean`](lean/TuDengFormal/FirstExitCarry.lean#L275) |
| 循环旋转归约 | 将任意同时含 0/1 的目标词旋转到 \(10v\) 形式 | `cyclicInputCount_rotate`, `cyclicInputCount_append_comm`, `exists_special_rotation` | [`FirstExitCarry.lean`](lean/TuDengFormal/FirstExitCarry.lean#L699) |
| 任意非常值目标词的半界 | 得到循环负侧输入个数不超过 \(2^{k-1}\) | `cyclicInputCount_bound_of_nonconstant` | [`FirstExitCarry.lean`](lean/TuDengFormal/FirstExitCarry.lean#L761) |
| 原始 Tu--Deng 计数与循环进位计数的对应 | 证明二进制值、Hamming 重量和进位方程的精确关系 | `carryRun_numeric`, `carryRun_weight`, `carryRun_negative_iff`, `chosenCarry_run` | [`FirstExitNat.lean`](lean/TuDengFormal/FirstExitNat.lean#L124) |
| 原计数与循环计数的双射 | 构造 `originalToPair` 和 `pairToOriginal`，证明两个有限集基数相等 | `originalToPair_mem`, `pairToOriginal_mem_and_inverse`, `originalToPair_injective_on`, `tdFinset_card_eq_cyclicPairs` | [`FirstExitNat.lean`](lean/TuDengFormal/FirstExitNat.lean#L329) |
| 最终计数结论 | 将循环半界传回原始模 \(2^k-1\) 计数 | `tuDengCount_eq_cyclicInputCount`, `tuDengCount_bound`, `tu_deng_conjecture_full` | [`FirstExitNat.lean`](lean/TuDengFormal/FirstExitNat.lean#L512) |

## 5. 各 Lean 文件的责任边界

### `TuDengDefinitions.lean`

只定义原问题，不包含证明技巧：

- `modulus k = 2^k - 1`；
- `hammingWeight k n`；
- `partner k t x`；
- `tuDengCount k t`；
- `TuDengConjecture k t`。

### `FirstExitCore.lean`

建立字典序、子序列边界语言、标记删除单射与半平面不等式。这是整个证明的
组合计数核心。

### `FirstExitBoundary.lean`

证明完整定向边界和字典序截断边界的追加递推。这些是 TeX 中二状态边界矩阵的
集合层版本。

### `FirstExitPolynomial.lean`

把边界集合转成二元枚举多项式，并证明关键交叉边界恒等式。同时证明商多项式
`Jenum` 就是显式语言 `langFinset` 的枚举多项式。

### `FirstExitFunctional.lean`

定义严格负半平面泛函 `phiNeg`，证明它对
`(X+Y-1)Jenum` 的作用精确等于语言层的 `halfplaneDefect`，最终得到
`cross_boundary_halfplane_bound`。

### `FirstExitCarry.lean`

建立进位扫描、活跃码、首出边界及重数之间的精确对应。先证明特殊旋转形式的上界，
再通过循环旋转推广到任意非常值二进制目标词。

### `FirstExitNat.lean`

把词语言形式化连回自然数、模 \(2^k-1\) 加法和 Hamming 重量。这里构造了原 Tu--Deng
有限集与循环进位有限集之间的正反映射，并给出最终定理。

## 6. 最终三个定理

### 精确计数等式

```lean
theorem tuDengCount_eq_cyclicInputCount {k t : ℕ} (hk : 0 < k)
    (ht : t < 2 ^ k - 1) :
    TuDeng.tuDengCount k t = cyclicInputCount (bitsWord k t)
```

### 数值上界

```lean
theorem tuDengCount_bound {k t : ℕ} (hk : 2 ≤ k)
    (ht₀ : 0 < t) (ht : t < 2 ^ k - 1) :
    TuDeng.tuDengCount k t ≤ 2 ^ (k - 1)
```

### 原猜想定义的完整封装

```lean
theorem tu_deng_conjecture_full (k t : ℕ) (hk : 2 ≤ k) :
    TuDeng.TuDengConjecture k t
```

## 7. 编译与公理审计

在 `final/lean` 目录中执行：

```bash
lake build
lake env lean AxiomAudit.lean
```

本交付目录已于 2026-07-16 在一个全新的 `.lake` 环境中独立执行上述命令：
首次 `lake build` 的 8596 个任务全部成功，随后的增量重建也成功。验证后已删除
12 GB 的 `.lake` 临时依赖与构建缓存，交付目录只保留源码和锁定版本的可复现配置。

形式化源文件中没有 `sorry` 或 `admit`。`AxiomAudit.lean` 对最终定理运行
`#print axioms`；审计结果仅包含：

```text
propext
Classical.choice
Quot.sound
```

不包含 `sorryAx`，也不依赖 `native_decide` 或有限参数穷举。
