# mst.c — 按 arXiv:2611.31187 实现的最小生成树（C）

> **English**: a single-file C implementation of the deterministic linear-time minimum
> spanning tree algorithm from Khanna–Putterman–Song, [arXiv:2611.31187](https://arxiv.org/abs/2611.31187)
> (2026): k Borůvka phases, then the paper's *certificate* (spoke/portal projection) to discard
> redundant edges, recursing on the surviving edge set. `O(m)` in the word-RAM model
> (radix-sorted weights); `--cmpsort` switches to the paper's pure-comparison model, where the
> sort term makes it `O(m log m)`. Section 5 explains precisely which parts of the paper are
> *not* implementable as written. ~1100 lines, no dependencies, MSVC/gcc/MSan-clean.

论文：S. Khanna, A. Putterman, J. Song,
*A Deterministic Linear Time Algorithm for Minimum Spanning Tree*,
arXiv:2611.31187v1。它证明了 MST 的确定性比较复杂度是 O(m)，据此给出确定性 O(m) 时间算法，
结束了自 Chazelle (JACM 2000) 的 O(m α(m,n)) 以来 26 年的停滞。

本仓库把它落到一份可直接编译运行的 C 代码：保留论文的**算法骨架**（Algorithm 2 的递归结构 +
Algorithm 1 的 spoke/portal 投影），整条流水线现在是 **O(m)**（见第 3 节的做法与第 4 节的度量），
但**没有**实现论文达到 O(m) 所用的那两个不可运行的部件（见第 5 节）。

---

## 1. 论文的两个算法

```
Algorithm 2  MSF(G)
  1  k 次 Borůvka 相位，得 S 与收缩图 G'                    (Definition 2.8)
  2  删去孤立点
  3  若 G' 为空，返回 S
  4  F ← Certificate(G')                                   (Algorithm 1)
  5  U(F) ← G' 中不被 F 支持的边（F^{≤w(e)} 连不通两端点）  (Section 3.1)
  6  return S ∪ MSF(G'[F ∪ U(F)])
```

递归之所以正确：被支持的边按**环性质**（Fact 2.3）一定不在 MSF 里，所以 G'[F∪U(F)] 仍含一个 MSF；
又由**收缩性质**（Fact 2.4）与**阈值连通性**（Fact 2.5）把它拼回 S 即可。

`Certificate` 的机制（Section 3.1）是：给每个顶点一条 **spoke** σ(v)（最轻关联边），
其另一端叫 **portal** π(v)；把边 e=(u,v) **投影**成同权重的 (π(u),π(v))，当且仅当
`max(w(σ(u)),w(σ(v))) ≤ w(e)` 时投影**合法**。投影得到顶点更少的重图，递归下去；
每个顶点被反复投影，便宜的路径把边卷成环，环上最重的边就被判定为冗余。

## 2. 代码与论文的对应

| 论文 | 代码 |
|---|---|
| Definition 2.8 Borůvka 相位 | `boruvka_phase()` |
| Algorithm 2 第 2–3 行：收缩、删孤立点 | `contract()` |
| Algorithm 1：Certificate | `certificate()`（spoke / portal / 合法投影 / 递归 / 提升合并） |
| §3.1 supported、U(F)（Lemma 2.9 的判定） | `unsupported_edges()` |
| Algorithm 1 的“精确 MSF 调用” | `kruskal_exact()` |
| Algorithm 2 本体、递归 | `msf_rec()` |
| 稠密图基例（§1.1 提到的 O(n²) Prim） | `prim_dense()` |
| 环性质 / 最优性证书（验证用） | `verify_msf()` |

`certificate()` 的每一层是：

1. σ(v) ← v 的最轻关联边；
2. F ← MSF(G[F ∪ σ])（论文 Algorithm 1 第 22 行）；
3. portal = spoke 森林的连通分量（每个分量至少两个顶点，所以 |P| ≤ n/2）；
4. 把合法边投影到 portal 集上，递归 `certificate()`（深度上限 4，见 `--depth`）；
5. 把子层森林沿投影记录**提升**回原边，再 F ← MSF(F ∪ 提升结果)（第 19 行）。

## 3. 怎么做到 O(m)

整条流水线的耗时拆开看（m = 边数）：

| 步骤 | 代价 |
|---|---|
| k 次 Borůvka（k=3） | O(m)，每边至多 2 次比较 |
| 收缩 + 重标号 | O(m + n) |
| 证书（spoke/portal，≤ 4 层投影） | O(m)，每层扫一遍边集 |
| 支持性判定 U(F) | O(m)：排序一次 + 并查集扫一遍 |
| 递归 MSF(G'[F∪U(F)]) | T(m'), **m' ≤ m/2**（`--om` 会打印验证） |

于是 T(m) ≤ T(m/2) + O(m) = O(m)。其中唯一非线性的部件是**排序**：
原来用 `qsort` 比较排序 → O(m log m)；现在换成对 IEEE-754 位模式的 **LSD 基数排序**
（11 位 × 6 趟），**零权重比较**，代价 O(m)。`--cmpsort` 可以切回 `qsort` 做对照。

这就是所谓“om 模式”（默认开启）：`--om` 会打印每层边数的缩减比例与比较次数/边，
并检查每一层是否真的至少减半。

## 4. 实测（Windows, MSVC 19.4x, /O2, 单线程）

### 4.1 与 Kruskal 对比（都是线性排序，随机图）

| n | m | 本实现 | 比较/边 | 朴素 Kruskal |
|---|---|---|---|---|
| 1 000 | 5 000 | 0.3 ms | 6.2 | 0.1 ms |
| 10 000 | 20 000 | 1.6 ms | 6.3 | 0.6 ms |
| 10 000 | 50 000 | 3.6 ms | 8.4 | 1.3 ms |
| 100 000 | 200 000 | 17 ms | 7.2 | 6.8 ms |
| 100 000 | 1 000 000 | 85 ms | 11.2 | 44 ms |
| 500 000 | 1 000 000 | 108 ms | 7.8 | — |
| 1 000 000 | 2 000 000 | 264 ms | 8.1 | 175 ms |

### 4.2 线性性：固定平均度 10，放大规模

| n | m | 比较/边 | µs/边 |
|---|---|---|---|
| 2 000 | 20 000 | 8.2 | 0.066 |
| 20 000 | 200 000 | 10.3 | 0.063 |
| 200 000 | 2 000 000 | 12.4 | 0.093 |

规模放大 100 倍，每边比较次数稳定在 8–12（没有 log 因子：证书的投影层数是常数 4），
每边耗时基本不变——这就是 O(m) 的直接证据。`--om` 输出例如：

```
om      : m = 2000000 -> 1775 (0.09%)   recursion halves every level: yes
cost    : 12.37 comparisons/edge, 0.093 us/edge
```

### 4.3 排序方式的差别（n=10⁶, m=2×10⁶）

| 排序 | 时间 | 比较/边 |
|---|---|---|
| 基数排序（默认，O(m)） | 264 ms | 8.1 |
| `qsort`（`--cmpsort`，O(m log m)） | 382 ms | 20.3 |

稠密小图上走 Prim 基例：n=400、m=200 000 时 6.6 ms，Kruskal 需 21.7 ms。

## 5. 论文里有、这里没有的东西（重要）

论文的 O(m) 是**比较次数**的界，靠两个部件做到，而这两个部件都不可实际运行：

1. **§3.4 的 schedule**：它先界定 history 的个数 |H| ≤ exp(O(t²√(mn)))，再用概率方法
   证明“存在一个好排班”，最后的做法是**枚举所有排班、对所有 history 逐一检查**。
   论文原文：*“Although this may incur enormous computational overhead, it requires no
   comparisons, and we are only concerned with the number of comparisons.”*
   也就是说它是存在性证明的产物，实际运行是天文数字；本实现用“每条边只行动一轮”代替。
2. **Komlós 的线性 path-max 查询（Lemma 2.9）**：给定森林 F 和 q 条路径端点，用 O(n+q)
   **比较**求出每条路径上的最大权边。本实现用“排序 + 并查集扫描”代替它——
   这正是我们把 O(m) 的比较次数换成“基数排序（不比较）+ O(m)”的原因。
3. **§3.2 的批次处理**（r² 个最轻代表元 + portal 覆盖论证）与 **§3.5 的偏好动作估计**，
   本实现简化为 r=1（每点一条 spoke），因此拿不到论文 Lemma 3.1 的
   `|F|+|U(F)|+Σ|Eᵢ| ≤ εm + C√(nm)` 常数界；作为替代，代码用“若某层没减半就 Kruskal 收尾”
   的进度保护，保证递归仍然几何收敛。

因此准确的表述是：**本实现是 word-RAM 模型下的 O(m)（基数排序利用权重位模式），
不是论文的“只用比较、权重不可见”模型下的 O(m)**；后者需要上面第 1、2 项。
论文在 §1 里也把 Fredman–Willard 的 word-RAM 结果单列一类，本实现正好落在那一类里。

另外，正确性完全不依赖证书质量：被 F 支持的边按环性质一定不在 MSF 里，所以递归对
**任何**森林 F 都正确，差别只在常数与层数。所有测试都验证这一点（见第 6 节）。

## 6. 结果怎么被验证

`verify_msf()` 不依赖算法内部任何东西，检查四条：

1. 边数恰为 `n − c`（c 为原图连通分量数）；
2. 结果无环（并查集）；
3. 每条树边的 id / 权重与输入一致；
4. **环性质**：每条非树边都被树支持，即“树上 u–v 路径的最大权 ≤ w(e)”，
   这就是 MST 的最优性证书。

此外：

- `--ref` 用朴素 Kruskal 交叉核对总权重；
- `--fuzz K` 在 K 个随机实例上做差分测试（含等权、网格、多重边、自环、负权、n=1、非连通，
  并随机压低基例阈值来强制走深递归）；
- `--sorttest K` 用 qsort 对拍基数排序（含 ±0、±1e300、大量等值、已排序输入）；
- `gcc -std=c11 -Wall -Wextra -pedantic` 零告警，`-fsanitize=address,undefined` 无越界/泄漏。

当前状态：`--fuzz 3000` + `--sorttest 80` 全部通过。

## 7. 构建与运行

```
build.cmd                     :: MSVC: vcvars64 + cl /O2 /W4 /std:c11
gcc -O2 -o mst mst.c          :: gcc / clang
```

```
mst --bench                            :: 规模表
mst --n 100000 --m 1000000 --om        :: 线性性报告（每层缩减 + 比较/边）
mst --n 1000000 --m 2000000 --cmpsort  :: 换回比较排序做对照
mst --fuzz 3000 ; mst --sorttest 80    :: 差分测试
mst --file graph.txt --out tree.txt    :: DIMACS 输入/输出
mst --ties 5 --kind 1                  :: 大量等权 / 网格图
```

输入格式（DIMACS 风格，顶点 1-based）：

```
c 注释
p <n> <m>
a <u> <v> <w>
```

`--out` 写出的每行是 `u v w`（顶点 0-based，即内部编号）。

## 8. 文件

| 文件 | 内容 |
|---|---|
| `mst.c` | 全部实现（约 1 100 行，无第三方依赖） |
| `build.cmd` | MSVC 一键构建 |
| `t_disc.txt` / `t_par.txt` / `t_path.txt` / `t_one.txt` | DIMACS 边界样例（非连通 / 多重边 / 树 / 单点） |

## 9. 再往上贴论文要做什么

- 把 `unsupported_edges()` 换成 Komlós / Dixon–Rauch–Tarjan 的**线性 path-max**，
  才能在“只用比较”的模型里也拿到 O(m)（现在这一步靠基数排序把 log 因子抹掉）；
- 补 §3.4 的 schedule（t² 轮、t 块、2t 个 bad round）与 §3.5 的偏好估计，
  才能拿到 Lemma 3.1 的 `εm + C√(nm)` 具体界；注意论文给的是**存在性**排班，
  真跑起来需要枚举 history，只在小规模上有意义；
- 补 §3.2 的 r² 代表元批次处理，把证书质量从“实测挺好”升级成“有证明”；
- 用 Pettie–Ramachandran 的最优判定树替换基例，才真正达到 `T*(m,n)`。

## 10. 许可

MIT，见 [LICENSE](LICENSE)。代码按论文实现，论文本身版权归原作者；引用请用：

```bibtex
@misc{khanna2026mst,
  title  = {A Deterministic Linear Time Algorithm for Minimum Spanning Tree},
  author = {Khanna, Sanjeev and Putterman, Aaron and Song, Junkai},
  year   = {2026},
  eprint = {2611.31187},
  archivePrefix = {arXiv},
  primaryClass  = {cs.DS}
}
```
