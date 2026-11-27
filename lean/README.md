# Refined BMV in Lean 4

这个 Lake 工程对应 2026 年 11 月 27 日北京时间 17:16 更新的 BMV 手稿。主定理直接使用所有矩阵字的归一化迹，矩阵维度任意，标量域为复数。

## 无条件定理

| 结论 | Lean 入口 | 矩阵假设 |
| --- | --- | --- |
| 字平均 `E(n,3)`，`n = 1,2,3,4,5,6` | `RefinedBMV.even_word_m3_one_through_six` | `A` 和 `B` 均为 Hermitian 半正定，允许奇异 |
| 字平均 `E(n,4)`，`n = 1,2,3,4,5,6,8` | `RefinedBMV.even_word_m4_family` | `A` 半正定，`B` 为任意 Hermitian 矩阵，允许不定 |
| `E(4,4)` 的合同变换形式 | `RefinedBMV.even_word_44_congruence` | `A = T²`，`X = TBT`，迹下界为 `Tr(X⁴)` |
| 指数迹下界 `L(n,3)`，`n = 1,2,3,4,5,6` | `RefinedBMV.exponential_m3_one_through_six` | 两个指数参数均为 Hermitian 矩阵 |
| 指数迹下界 `L(n,4)`，`n = 1,2,3,4,5,6,8` | `RefinedBMV.exponential_m4_family` | 两个指数参数均为 Hermitian 矩阵 |
| 有限字平均收敛到指数迹在零点的三阶实导数 | `RefinedBMV.wordAverage_tendsto_duhamel` | 任意有限复矩阵 `H` 和 `B` |

`QuarticFamily.lean` 使用新版手稿的三个新整数证书 `(5,4)`、`(6,4)` 和 `(8,4)`。Lean 对所有尾随主子式验证了关于 `ac` 和 `(a-c)^2` 的精确多项式恒等式，并用 Schur 补推出两个 Gram 块正半定。

`(5,3)` 的双 Cauchy 证书采用重建出的有理 Gram 块，Lean 精确检查了 LDLᵀ 和循环多项式恒等式。`(3,4)` 的整数块与云盘校验脚本一致。

## 需要标量符号条件的定理

| 结论 | Lean 入口 | 尚需证明的条件 |
| --- | --- | --- |
| 完整有限三阶族 `E(n,3)` | `RefinedBMV.even_word_m3_of_uniform_mixedDensity` | 对 `0 ≤ ε ≤ 1/7`，`MixedDensityNonneg ε` |
| 有限三阶指数下界 `L(n,3)` | `RefinedBMV.exponential_m3_of_mixedDensity` | 对该阶 `n`，`MixedDensityNonneg (1/n)` |
| Duhamel 三阶导数下界 | `RefinedBMV.duhamel_of_uniform_mixedDensity` | 与完整有限三阶族相同的标量条件 |
| Duhamel 谱系数下界 | `RefinedBMV.duhamel_spectral_of_mixedDensity` | `MixedDensityNonneg 0` |

混合偏导条件是对所有 `s > 0`、`v > 0` 证明 `mixedDensity ε s v ≥ 0`。对角的严格正性、连续性以及两侧极限已在 Lean 证明。矩阵半正定性通过有限矩形差分得到。导数版 Duhamel 结论通过有限多项式的三阶导数和局部一致极限得到。

原 Python/C++ 程序复跑通过了 236,083 个统一区间盒和 7,292 个 Duhamel 专用区间盒。这些记录依赖外部区间计算和手稿的解析尾界。Lean 仍需核验这些区间包含性与尾界。Duhamel 的单纯形积分等式、对数极限、依赖一般 Araki–Lieb–Thirring 的对偶字不等式、等号条件和新版的奇阶多项式障碍也仍待形式化。

## 复现

使用 Elan 安装 `lean-toolchain` 中的 Lean 4.28.0。Mathlib 版本固定在 `lake-manifest.json`。首次构建可下载 Mathlib 预编译缓存。

```sh
lake exe cache get Mathlib/Tactic.lean \
  Mathlib/Analysis/Matrix/Order.lean \
  Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean \
  Mathlib/Analysis/Calculus/LHopital.lean \
  Mathlib/Analysis/Complex/LocallyUniformLimit.lean \
  Mathlib/Analysis/Complex/RealDeriv.lean \
  Mathlib/Algebra/Polynomial/Eval/Degree.lean
lake build
lake env lean Verify.lean
```

`Verify.lean` 输出主定理的传递公理依赖。`verification.txt` 记录构建和公理检查结果。

## 资料版本

- 云盘 `refined_bmv_m3_m4_arxiv.tex`，北京时间 2026-11-27 17:16，SHA-256 `9892a9e271e86046ee20f7459132078e9c501c6f255460a99dfa007e72c2cd92`。[手稿](../manuscripts/refined_bmv_m3_m4_arxiv.tex)
- 云盘 `verify_m4_family_integer_gram.py`，SHA-256 `d5dc7ef10f52f1c96810f4d24b8cc089de84cef624fe576a357d4df103187901`。[四阶证书](../verify_m4_family_integer_gram.py)
- GitHub `NiuVector/Refined-BMV-Conjecture`，提交 `7fd3f1d84bcfe9cadd738bff4b5409d6ad55ea53`。[仓库快照](https://github.com/NiuVector/Refined-BMV-Conjecture/tree/7fd3f1d84bcfe9cadd738bff4b5409d6ad55ea53)
- 矩形差分、迹幂和 Trotter 证明复用并适配了 Apache 2.0 许可的公开形式化。原作者声明和许可证在对应源码和 `RefinedBMV/Supporting/LICENSE-Apache-2.0.txt`。[trureturing](https://github.com/the-omega-institute/trureturing/tree/51dca4f1542baa532983864568d6a8ca3470e745)
