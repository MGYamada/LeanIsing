# LeanIsing

Lean 4 だけで書いた Ising 模型の Metropolis 法シミュレーションと、横磁場 Ising 模型の経路積分量子モンテカルロ法です。
乱数も確率もすべて**厳密な有理数**（Lean core の `Rat`）で扱い、浮動小数点数は一切使いません。
そのうえで、**シミュレーションが実際に動かしているマルコフ連鎖**が詳細釣り合いとエルゴード性を満たし、
任意の初期分布から目標の分布（古典模型では Boltzmann 分布、量子模型では経路積分の重みによる世界線の分布）へ
幾何的に収束することを、Lean のカーネルで証明しています。

- シミュレーション本体、乱数生成器、証明、ビルド設定（`lakefile.lean`）まで、すべて Lean で書いています。
- 外部ライブラリには依存しません（Lean core だけを使います。Mathlib も使いません）。
- `sorry` も `native_decide` も使いません。主定理が Lean の標準公理以外に依存しないことは、ビルドのたびに検査します。

## 実行

必要なのは [elan](https://github.com/leanprover/elan) だけです（`lean-toolchain` に従って Lean 4.35.0 が入ります）。

```sh
lake build                          # シミュレーション・証明・監査・テストをまとめてビルド
lake exe ising                      # 24×24 格子で温度スキャン（約 13 秒）
lake exe ising -L 32 -T 2.269 --show            # 臨界温度付近、最終配位も表示
lake exe ising -x 70/169,2/5        # 温度を x = exp(-2/T) の有理数で直接指定
lake exe ising -L 4 --exact --sweeps 20000      # 全 65536 配位の和による厳密解と比較
lake exe ising --help
lake exe ising --quantum            # 横磁場 Ising 模型（16 サイトの環、M = 16、β = 4）で Γ をスキャン
lake exe ising --quantum -N 4 -M 8 --beta 2 --exact --sweeps 20000   # 同じ M での厳密値と比較
lake exe ising --quantum --help
```

実行例（`lake exe ising`、seed = 1）：

```
      T x               T_x          D            ⟨e⟩         ⟨|m|⟩      U₄    受理率     m_∞
----------------------------------------------------------------------------------------------
 1.5000 24/91        1.5006       91^4    -1.9508(11)     0.9864(3)   0.667  0.013   0.986
 2.0000 32/87        1.9997       87^4    -1.7400(44)    0.9077(35)   0.664  0.081   0.911
 2.2000 27/67        2.2006       67^4   -1.5280(185)   0.7419(402)   0.622  0.157   0.784
 2.2690 41/99        2.2687       99^4   -1.4411(200)   0.6868(354)   0.614  0.189   0.421
 2.3500 38/89        2.3500       89^4   -1.3451(183)   0.5980(388)   0.581  0.227   0.000
 2.5000 31/69        2.4996       69^4    -1.1097(75)   0.2683(227)   0.296  0.322   0.000
 3.0000 19/37        3.0008       37^4    -0.8204(46)    0.1278(87)   0.161  0.460   0.000
 3.5000 48/85        3.4999       85^4    -0.6542(25)    0.0805(21)   0.055  0.551   0.000
```

`⟨e⟩` は 1 サイトあたりのエネルギー、`⟨|m|⟩` は磁化の絶対値、`U₄` は Binder 比、括弧内は最終桁の標準誤差です。
`m_∞` は無限系の自発磁化の厳密解（Onsager–Yang）で、低温では `⟨|m|⟩` とよく一致します。
4×4 格子では、全配位の和で求めた厳密な熱平均とも誤差の範囲で一致します（`--exact`）。

## 厳密有理数で Metropolis 法を書く

### 温度を有理数で指定する

強磁性 Ising 模型 `E(σ) = -J Σ_⟨ij⟩ s_i s_j` の Boltzmann 重みは、`x = exp(-2βJ)` とおくと

```
exp(-βE(σ)) = exp(βJ·|bonds|) · x ^ (不満足ボンドの数)
```

と書けます。定数倍は確率に効かないので、重みは `x ^ unsat σ` で十分です。そこで温度を `β` ではなく
**有理数 `x ∈ (0, 1)`** で指定すると、Boltzmann 重みも、Metropolis の受理確率 `min(1, x^Δ)` も、すべて厳密な有理数になります。
（臨界点は `x_c = √2 − 1`。その最良有理近似 `41/99`、`70/169`（Pell 数の比）などが使えます。）
`-T` で温度を与えた場合は、`exp(-2/T)` を有理数の級数で計算し、分母 100 以下の最良有理近似を `x` とします。
表の `T_x` は、その `x` に厳密に対応する温度 `-2/ln x` です。

### 一様乱数を有理数 `u = k/D` で作る

受理判定には一様乱数 `u = k / D`（`k ∈ {0, 1, …, D−1}`）を `Rat` として作り、`u < 受理確率` を**厳密に比較**します。
分母は `D = (x の分母)^(最大次数)`（正方格子なら `q^4`）にとります。受理確率 `x^Δ`（`Δ ≤ 4`）の分母はどれも `D` を割り切るので、

```
#{k < D : k/D < x^Δ} / D = x^Δ        （丸め誤差なし）
```

が成り立ちます。つまり、**有限個の乱数格子の上で、受理確率がちょうど再現されます**。
`x = 2/5` なら `D = 625` で十分で、`u` が 625 通りしかなくても、得られるマルコフ連鎖は Metropolis 法そのものです。
（テストでは、`D` が足りないと遷移確率が一致しなくなることも確かめています。）

整数 `k` は SplitMix64 の 64 ビット語から**棄却法**で作るので、`[0, D)` の上で偏りがありません
（採用した語の中で各剰余がちょうど同じ回数現れることを `rejection_exact` として証明しています）。

## 横磁場 Ising 模型の量子モンテカルロ法

`H = -J Σ_⟨ij⟩ σᶻ_i σᶻ_j - Γ Σ_i σˣ_i` を Trotter 数 `M`、`ε = β/M` で分解すると
`Z_M = Tr (e^{εJΣσᶻσᶻ} e^{εΓΣσˣ})^M` になります。`e^{aσˣ} = cosh a · (1 + tanh a · σˣ)` なので、
`σᶻ` 基底での転送行列の要素は、定数倍を除いて

```
T(s, s') = x^{unsat(s)} · y^{#{i : s_i ≠ s'_i}}、   x = e^{-2εJ}、 y = tanh(εΓ)
```

です。`x` と `y` を有理数にとれば、世界線 `(s_0, …, s_{M-1})` の重み `Π_τ T(s_τ, s_{τ+1})` も厳密な有理数になります。
これは空間 × 虚時間の格子上で、空間方向のボンドの因子が `x`、虚時間方向のボンドの因子が `y` の
2 層の Ising 模型の重みと同じなので（`trotter_weight`）、その Metropolis 法が経路積分量子モンテカルロ法になります。
`M = 1` では虚時間方向のボンドが自己ループになり、古典模型に戻ります（`pathWeight_one`）。

実行例（`lake exe ising --quantum -N 4 -M 8 --beta 2 --gamma 0.5,1,2 --sweeps 20000 --therm 1000 --exact`）：

```
     Γ y               Γ_y         ⟨σᶻσᶻ⟩          ⟨σˣ⟩       ⟨|m_z|⟩        e    受理率    ⟨σᶻσᶻ⟩ 厳密    ⟨σˣ⟩ 厳密
-----------------------------------------------------------------------------------------------------------------
 0.500 24/193       0.5000     0.9334(57)    0.2821(71)    0.9622(40)  -1.0744  0.028       0.9364     0.2780
 1.000 12/49        0.9999     0.7375(58)    0.5882(65)    0.8215(55)  -1.3256  0.135       0.7373     0.5873
 2.000 61/132       2.0000     0.3771(32)    0.9348(21)    0.4102(42)  -2.2467  0.451       0.3782     0.9332
```

「厳密」の列は、`2^N × 2^N` の転送行列を `M` 回掛けて求めた、**同じ `M` での**厳密な期待値です（`LeanIsing/QuantumExact.lean`）。
モンテカルロ法の結果は誤差の範囲で一致します。

注意：定常分布は **Trotter 分解した**経路積分の測度そのもので、量子系の熱平衡状態との差（Trotter 誤差）は `O((β/M)²)` 残ります。
たとえば上の `Γ = 1` の厳密エネルギーは `M = 4, 8, 16, 32` で −1.456、−1.325、−1.286、−1.276 と `M → ∞` へ収束していきます。
更新は単一スピン反転だけなので、`M` が大きい（`y` が小さい）ほど受理率が下がり、相関時間が長くなります。

### 古典模型から量子模型へ、証明を保ったまま移行した手順

各段階で `lake build`（証明・監査・テスト）がすべて通る状態を保ち、定常分布の存在を一度も失わずに移行しました。

1. **一般の重み**：Metropolis 核を任意の正の重み `w` について定義し直し（`metropolis w`、`normalize w`）、
   詳細釣り合い・定常性・既約性・エルゴード性・収束を一般の `w` で証明する。古典模型の `kernel G x` は
   `metropolis (weight G x)` と定義上等しく、既存の定理の主張は変わらない。
   エルゴード性の仮定は「重みが減る反転が 1 つある」だけになる。
2. **層つき模型**：ボンドの層ごとに因子 `x_l` をもつ模型 `Model` を入れる。古典模型は 1 層の場合
   （`toModel_kernel`）。
3. **層つき模型の実行系**：局所比 `Π_l x_l^{agree_l} / x_l^{disagree_l}` から受理確率 `A` を計算する。
   層が複数あると分母に因子の分子も現れるので、一様乱数の分母を `A` 自身の分母 `D = A.den` に合わせ、
   `u = k/D` との厳密比較で `P(u < A) = A` を丸めなしに保つ（`layered_exact`）。
4. **横磁場 Ising 模型**：Trotter 格子を 2 層の模型として作り、重みが転送行列の要素の積であることと
   （`trotter_weight`、`transfer_eq_tensor`）、QMC 連鎖の性質（`qmc_simulation`）を示す。
5. **実行ファイル**：`--quantum` モードと、転送行列による同じ `M` での厳密値との比較。

## 何が証明されているか

主定理は [`Proofs/Theorems.lean`](Proofs/Theorems.lean)、[`Proofs/Convergence.lean`](Proofs/Convergence.lean)、
[`Proofs/Quantum.lean`](Proofs/Quantum.lean) にあります。
正方格子でのいちばん強い形は次の 2 つです。

```lean
/-- L ≥ 2、0 < x < 1 なら、シミュレーションが動かしている連鎖は
    Boltzmann 分布について詳細釣り合いを満たし、エルゴード的である。 -/
theorem square_simulation (L : Nat) (hL : 2 ≤ L) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1) :
    Chain.DetailedBalance (boltzmann (Lattice.square L) x)
        (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D) ∧
      Chain.Ergodic (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D)

/-- 同じ条件で、その連鎖は任意の初期分布から Boltzmann 分布へ幾何的に収束する。 -/
theorem square_simulation_converges (L : Nat) (hL : 2 ≤ L) (x : Rat) (hx0 : 0 < x) (hx1 : x < 1) :
    Chain.GeometricConvergence (boltzmann (Lattice.square L) x)
        (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D) ∧
      Chain.Converges (boltzmann (Lattice.square L) x)
        (inducedKernel (Lattice.square L) x (Sim.make (Lattice.square L) x).D)
```

ここで `inducedKernel G x D σ τ` は、**実装の 1 ステップ `step`** に一様乱数（サイト `i ∈ Fin n` と `u = k/D`）を与えたとき、
`σ` が `τ` に移る確率（`n·D` 通りの乱数のうち `τ` に移るものの割合）です。
理想化したモデルではなく、プログラムが実行している遷移そのものについての定理です。

| 定理 | 内容 | 条件 |
| --- | --- | --- |
| `metropolis_stochastic` | 仕様の Metropolis 核は確率行列（非負・行和 1） | 任意のグラフ、`0 < x` |
| `metropolis_detailed_balance` | **詳細釣り合い** `π(σ)P(σ→τ) = π(τ)P(τ→σ)` | 任意のグラフ、`0 < x` |
| `metropolis_stationary` | Boltzmann 分布は定常分布 `πP = π` | 任意のグラフ、`0 < x` |
| `metropolis_irreducible` | **既約性**：どの配位からどの配位へも `n` ステップ以内に正の確率で移れる | 任意のグラフ、`0 < x` |
| `metropolis_ergodic` | **エルゴード性**：`m ≥ 2n` のどの `m` でも、すべての `P^m(σ→τ)` が正 | `0 < x < 1`、自己ループでないボンドが 1 本以上 |
| `metropolis_geometric` | **幾何収束**：任意の初期分布 `μ` で `Σ_τ \|μP^t(τ) − π(τ)\| ≤ 2ρ^⌊t/m⌋`（`m > 0`、`0 ≤ ρ < 1`） | 同上 |
| `metropolis_converges` | **収束**：任意の初期分布 `μ` で `μP^t(τ) → π(τ)`（`t → ∞`） | 同上 |
| `simulation_exact` | 実装の遷移確率 `inducedKernel` = 仕様の核 `kernel` | 任意のグラフ、`0 < x ≤ 1` |
| `simulation_*` | 上の性質を実装の連鎖について | 同上 |
| `rejection_exact` | 乱数の棄却法は各値をちょうど同じ回数出す | |
| `general_*` | 任意の正の重み `w` の Metropolis 核について、上の性質（エルゴード性・収束は「重みが減る反転がある」とき） | `w > 0` |
| `layered_exact` | 層つき模型の実装の遷移確率 = 仕様の核 | 因子がすべて正 |
| `trotter_weight` | 2 層の Trotter 模型の重み = 世界線の重み `Π_τ T(s_τ, s_{τ+1})` | |
| `transfer_eq_tensor` | 横磁場の因子は `1 + yσˣ` のテンソル積 | |
| `pathWeight_one` | `M = 1` では古典模型の重み | |
| `qmc_exact` | QMC の実装の遷移確率 = 世界線の重みに対する Metropolis 核 | `0 < x`、`0 < y` |
| `qmc_simulation` | QMC 連鎖は世界線の分布について詳細釣り合い・定常・エルゴード的・幾何収束・収束 | `0 < x < 1`、`0 < y ≤ 1`、`M ≥ 1` |

経路積分の恒等式 `Σ_世界線 Π_τ T(s_τ, s_{τ+1}) = Tr T^M`（世界線の分布の規格化定数が Trotter 分解した分配関数であること）は、
小さな系での数値検査（`Tests/QuantumTests.lean`）にとどめ、一般には証明していません。

エルゴード性は、有限状態マルコフ連鎖としての正則性（既約かつ非周期的）として述べています。
定常分布への収束は Perron–Frobenius の定理を使わずに、Doeblin の議論で直接証明しています（下の「証明のしくみ」）。
収束先が Boltzmann 分布なので、定常分布が Boltzmann 分布だけであることもここから直ちに従います（定理としては述べていません）。
なお `x = 1`（無限温度）では、すべての反転が受理されるため連鎖は周期 2 になり、エルゴード性は成り立ちません
（既約性は成り立ちます）。テストでこれも確かめています。

### 前提（信頼する部分）

定理の意味は [`LeanIsing/Spec.lean`](LeanIsing/Spec.lean)（約 160 行）だけで決まります。

- `Graph`：サイト `Fin n` とボンドのリスト。`Config n = Vector Bool n`（`true` が上向き）。
- `unsat σ`：両端が逆向きのボンドの数。エネルギーは `E = 2·unsat − |bonds|`。
- `weight G x σ = x ^ unsat σ`、`boltzmann G x σ = weight / Z`、`Z = Σ_σ weight`（全 `2^n` 配位の和）。
- `accept G x σ i = min 1 (weight (flip σ i) / weight σ)`。
- `kernel G x σ τ`：サイト `i` を確率 `1/n` で選び、確率 `accept` で反転、さもなくばとどまる、の遷移確率。
- `Chain.Stochastic` / `DetailedBalance` / `Stationary` / `Irreducible` / `Ergodic`：一般の遷移行列についての性質。
  `Chain.pow P m` は遷移行列の `m` 乗。
- `normalize w`、`acceptW w`、`metropolis w`：一般の正の重み `w` に対する分布と Metropolis 核。
  古典模型の `boltzmann G x`、`accept G x`、`kernel G x` は `w = weight G x` の場合。
- `Model`（ボンドの層と因子の組）、`Model.weight = Π_l x_l ^ unsat_l`、`Model.kernel`、`Model.boltzmann`。
- [`LeanIsing/Quantum.lean`](LeanIsing/Quantum.lean)：`transfer`（Trotter 転送行列）、`pathWeight`（世界線の重み）、
  `trotter G M x y`（2 層の模型）、`pathDistribution`（世界線の分布）。
- `Chain.IsDistribution`（非負で総和 1）、`Chain.evolve P μ t`（`t` ステップ後の分布 `μP^t`）、
  `Chain.l1Dist`（L¹ 距離）、`Chain.Converges` / `GeometricConvergence`：収束の主張。

加えて、`inducedKernel`（[`LeanIsing/Engine.lean`](LeanIsing/Engine.lean)）と `Layered.inducedKernel`
（[`LeanIsing/Layered.lean`](LeanIsing/Layered.lean)）が「シミュレーションの 1 ステップの遷移確率」であることを信頼します。
シミュレーション `Sim.stepM` は、乱数 `i`、`k` を引いて `Sim.stepPure` を呼ぶだけで、その結果が
`step x (G.nbrs i) σ i (k / D)` に等しいことは `Sim.stepPure_fst` として証明しています。
証明の外に残る前提は、(1) 擬似乱数（SplitMix64）が一様な 64 ビット語の列とみなせること、
(2) 乱数を引く部分（`Uniform.sample` とその `UInt64` 演算）が `rejection_exact` の述べる棄却法どおりに動くこと
（約 20 行のコードを読んで確認する部分）、(3) Lean のコンパイラと実行時系、です。

### 証明のしくみ

```
Spec（仕様：Boltzmann 分布と Metropolis 核）
  ▲  detailed_balance / stationary / irreducible / ergodic       (Proofs/DetailedBalance, Ergodicity)
  ▲  metropolis_geometric / metropolis_converges                  (Proofs/Convergence)
  ▲  inducedKernel_eq：実装の遷移確率 = 仕様の核                   (Proofs/Exactness)
Engine（実装：近傍だけで受理確率を計算し、u = k/D と厳密比較）
```

- **詳細釣り合い**：サイト `i` ごとの寄与 `w(σ)·[flip σ i = τ]·min(1, w(τ)/w(σ)) = [flip σ i = τ]·min(w(σ), w(τ))` が
  `σ ↔ τ` について対称（`flip σ i = τ ↔ flip τ i = σ`）であることから従います。
- **定常性**：詳細釣り合いと、各行の和が 1 であること（全配位のリストに重複がないことを使う）から従います。
- **既約性**：食い違うスピンを 1 個ずつ反転していけばよく、各反転の受理確率は `w > 0` なので正です。
- **エルゴード性**：全上向き配位でボンドの端点を反転すると不満足ボンドが増えるので、受理確率は `x^k < 1`、
  つまりその場にとどまる確率が正です。`σ → 全上向き（≤ n 歩）→ 足踏み → τ（≤ n 歩）` とつなぐと、
  `2n` 以上のどのステップ数でも正の確率で `σ` から `τ` に移れます。
- **収束**（Doeblin の議論）：`P^m`（`m = 2n`）の全成分の共通の下界 `δ > 0` をとると、和が 0 のベクトル `v` について
  `Σ_τ |(vP^m)(τ)| ≤ (1 − Nδ) Σ_σ |v(σ)|` が成り立ちます（`N = 2^n`、`l1_contract`）。
  `(vP^m)(τ) = Σ_σ v(σ)(P^m(σ→τ) − δ)` と書き直して三角不等式を使うだけです。
  `v = μP^t − π` は和が 0 で、定常性から `μP^{t+m} − π = (μP^t − π)P^m` なので、`m` ステップごとに
  距離が `ρ = 1 − Nδ < 1` 倍以下に縮みます（`geometric_of_primitive`）。`ρ^k → 0` は Bernoulli の不等式から従います。
  この部分は、確率行列・定常分布・ある `m > 0` での `P^m > 0` だけを仮定する、一般の有限マルコフ連鎖の定理です。
- **実装の厳密性**：(1) 反転による不満足ボンドの変化は近傍だけで決まる（`unsat_flip`）、
  (2) したがって近傍から計算した受理確率は仕様の `min(1, w'/w)` に等しい（`acceptLocal_eq`）、
  (3) `D` の選び方から `受理確率 × D` は整数で、`k/D < 受理確率` となる `k` はちょうどその個数（`count_site`）。

### 公理と監査

主定理は Lean の標準公理 `propext`・`Classical.choice`・`Quot.sound` だけに依存します
（`Rat` の補題や `simp`・`grind`・`omega` がこれらを使うため。leankoban のような公理ゼロではありません）。
[`Proofs/Audit.lean`](Proofs/Audit.lean) が `lake build` のたびに、22 個の主定理の**主張が期待どおりであること**と、
主定理と補助定理が**標準公理以外（`sorryAx`、`native_decide` の `Lean.ofReduceBool` など）に依存しないこと**を検査し、
違反があればビルドを失敗させます。

```sh
lake build Proofs.Audit
# info: 監査 OK: 22 個の主定理の主張は期待どおりで、これらと補助定理 19 個は
#       標準公理（propext, Classical.choice, Quot.sound）だけに依存する（sorry・native_decide なし）。
```

## ファイル構成

```
lakefile.lean                  ビルド設定（Lean DSL）
LeanIsing/Spec.lean            仕様（信頼の核）：模型・Boltzmann 分布・Metropolis 核・連鎖の性質
LeanIsing/Rng.lean             SplitMix64、棄却法による一様乱数、厳密有理数の乱数 u = k/D
LeanIsing/Lattice.lean         正方格子（周期境界）と 1 次元の環
LeanIsing/Engine.lean          実装：近傍の受理確率、step、スイープ、統計、inducedKernel
LeanIsing/Layered.lean         層つき模型の実装（受理確率の分母に合わせた乱数格子）
LeanIsing/Quantum.lean         横磁場 Ising 模型の経路積分表示（仕様）：転送行列・世界線の重み・Trotter 格子
LeanIsing/QuantumExact.lean    小さな量子系の厳密値（転送行列の積）
LeanIsing/QuantumApp.lean      実行ファイルの --quantum モード
LeanIsing/Exact.lean           小さな系の厳密解（全配位の和、状態密度）
LeanIsing/Numeric.lean         表示用の数値計算（有理数の級数による exp・ln、最良有理近似、Onsager 解）
LeanIsing/App.lean, Main.lean  実行ファイル
Proofs/Lemmas.lean             反転・全配位・和の補題
Proofs/DetailedBalance.lean    詳細釣り合い・確率行列・定常性（一般の重み）
Proofs/Ergodicity.lean         既約性・エルゴード性（一般の重み）
Proofs/Exactness.lean          実装の遷移確率 = 仕様の核
Proofs/Convergence.lean        定常分布への幾何収束（Doeblin の議論）
Proofs/Model.lean              層つき模型の詳細釣り合い・エルゴード性・収束、古典模型 = 1 層
Proofs/Layered.lean            層つき模型の実装の遷移確率 = 仕様の核
Proofs/Quantum.lean            世界線の重み・テンソル積・M = 1・量子モンテカルロ法の主定理
Proofs/Theorems.lean           主定理（実装・正方格子への適用、棄却法）
Proofs/Audit.lean              主張と公理の監査
Tests/EngineTests.lean         小さな系での数値検査（ビルド時に評価する #guard）
Tests/QuantumTests.lean        量子モンテカルロ法の数値検査（経路積分の恒等式 Σ Π T = Tr T^M を含む）
```
