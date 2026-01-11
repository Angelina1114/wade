/-
Chapter 1: The Real Number System
-/

import Mathlib.Data.Real.Basic -- 實數的基本類型
import Mathlib.Data.Real.Archimedean -- 實數的阿基米德性質


namespace WadeAnalysis


/-
## 第一章：實數系统 (Chapter 1: The Real Number System)

### Lean 基本語法說明

1. **類型註解語法**：`(值 : 類型)`
   - 例如：`(1 : ℝ)` 表示將數字 1 標註為實數類型

2. **檢查命令語法**：`#check <表達式>`
   - 用於檢查表達式的類型，不會執行程式碼

3. **定理聲明語法**：
   - `example (參數列表) : 命題 := 證明` - 匿名定理
   - `theorem 名稱 (參數列表) : 命題 := 證明` - 命名定理
   - `lemma 名稱 (參數列表) : 命題 := 證明` - 引理（與 theorem 相同）

4. **參數列表語法**：`(變數1 : 類型1) (變數2 : 類型2) ...`
   - 可以簡寫為 `(a b c : ℝ)` 表示 a, b, c 都是實數類型

5. **邏輯連接符**：
   - `→` 或 `→` - 蘊含（implies）
   - `↔` - 雙向蘊含（若且唯若，iff）
   - `∧` - 邏輯與（and）
   - `∨` - 邏輯或（or）
   - `¬` - 邏輯非（not）

6. **關係符號**：
   - `=` - 等於
   - `≤` - 小於等於
   - `≥` - 大於等於
   - `<` - 小於
   - `>` - 大於

7. **證明語法**：`:= 證明項`
   - 可以直接使用已有的定理，如 `add_comm a b`
   - 也可以使用策略（tactics）進行證明

### 1.1 引言 (Introduction)

在 Lean 中，實數系統已經透過 Mathlib 定義好了。
我們可以直接使用 `ℝ` (Real) 類型。
-/

-- 實數的基本類型
-- 語法：`#check <表達式>` - 檢查表達式的類型
-- 這會顯示表達式的類型資訊，用於驗證類型是否正確
#check ℝ
-- `ℝ` 是實數的類型，類型本身也是類型，所以會顯示 `Type`

-- 語法：`(值 : 類型)` - 類型註解（type annotation）
-- 這裡將數字 1 標註為實數類型
#check (1 : ℝ)
-- 這會顯示 `1 : ℝ`，表示 1 是實數類型

-- π 需要匯入三角函數模組，這裡先註解掉
-- #check (π : ℝ)

/-
### 1.2 有序域公理 (Ordered Field Axioms)

實數滿足有序域的所有公理。在 Lean 中，這些都已經內建了。

#### 公設語法說明

在 Lean 中，公設（axioms）通常以定理（theorem）或類型類（type class）的形式存在。
下面列出各個公設的語法結構：

1. **加法公理**
   - 交換律：`∀ a b : ℝ, a + b = b + a`
   - 結合律：`∀ a b c : ℝ, (a + b) + c = a + (b + c)`
   - 單位元（零元）：`∀ a : ℝ, a + 0 = a` 和 `∀ a : ℝ, 0 + a = a`
   - 逆元（負元）：`∀ a : ℝ, a + (-a) = 0` 和 `∀ a : ℝ, (-a) + a = 0`

2. **乘法公理**
   - 交換律：`∀ a b : ℝ, a * b = b * a`
   - 結合律：`∀ a b c : ℝ, (a * b) * c = a * (b * c)`
   - 單位元（單位元）：`∀ a : ℝ, a * 1 = a` 和 `∀ a : ℝ, 1 * a = a`
   - 逆元（倒數，對非零元）：`∀ a : ℝ, a ≠ 0 → a * a⁻¹ = 1`

3. **分配律**
   - 左分配律：`∀ a b c : ℝ, a * (b + c) = a * b + a * c`
   - 右分配律：`∀ a b c : ℝ, (a + b) * c = a * c + b * c`

4. **序公理**
   - 全序性：`∀ a b : ℝ, a ≤ b ∨ b ≤ a`
   - 傳遞性：`∀ a b c : ℝ, a ≤ b → b ≤ c → a ≤ c`
   - 反身性：`∀ a : ℝ, a ≤ a`
   - 加法保序：`∀ a b c : ℝ, a ≤ b → a + c ≤ b + c`
   - 乘法保序（正數）：`∀ a b c : ℝ, 0 ≤ c → a ≤ b → a * c ≤ b * c`

5. **完備性公理**
   - 上確界存在性：有上界的非空集合必有上確界
   - 語法：`∀ s : Set ℝ, s.Nonempty → BddAbove s → ∃ x : ℝ, IsLUB s x`
-/

-- ============================================
-- 1. 加法公理 (Addition Axioms)
-- ============================================

-- 公設 1.1：加法交換律 (Additive Commutativity)
-- 語法：`∀ (變數 : 類型), 命題` - 全稱量詞（for all）
-- `∀ a b : ℝ` 是 `∀ a : ℝ, ∀ b : ℝ` 的簡寫
-- 命題：`a + b = b + a` 表示加法滿足交換律
-- 在 Lean 中透過 `add_comm` 定理實作

-- 公設 1.2：加法結合律 (Additive Associativity)
-- 語法：`(a + b) + c = a + (b + c)` - 括號表示運算順序
-- 命題表示：無論先加哪兩個，結果都相同
-- 完整語法：`example (a b c : ℝ) : (a + b) + c = a + (b + c) := add_assoc a b c`
-- `(a b c : ℝ)` - 聲明三個實數變數
-- `(a + b) + c = a + (b + c)` - 要證明的等式
-- `add_assoc` - 加法結合律定理，參數順序對應：`add_assoc a b c`

-- 公設 1.3：加法單位元（零元）(Additive Identity)
-- 語法：`0 : ℝ` 表示實數零
-- 命題：`a + 0 = a` 表示零是加法的單位元
-- `add_zero` 定理：`a + 0 = a`

-- 公設 1.4：加法逆元（負元）(Additive Inverse)
-- 語法：`-a` 表示 a 的加法逆元（負數）
-- 命題：`a + (-a) = 0` 表示每個數都有加法逆元
-- `add_neg_cancel` 定理：`a + (-a) = 0`

-- ============================================
-- 2. 乘法公理 (Multiplication Axioms)
-- ============================================

-- 公設 2.1：乘法交換律 (Multiplicative Commutativity)
-- 語法：`a * b = b * a` - 乘法滿足交換律

-- 公設 2.2：乘法結合律 (Multiplicative Associativity)
-- 語法：`(a * b) * c = a * (b * c)` - 乘法滿足結合律

-- 公設 2.3：乘法單位元（單位元）(Multiplicative Identity)
-- 語法：`1 : ℝ` 表示實數一
-- 命題：`a * 1 = a` 表示一是乘法的單位元
-- `mul_one` 定理：`a * 1 = a`

-- 公設 2.4：乘法逆元（倒數，對非零元）(Multiplicative Inverse)
-- 語法：`a⁻¹` 或 `1 / a` 表示 a 的乘法逆元（倒數）
-- 語法：`a ≠ 0` 表示 a 不等於零
-- 語法：`→` 表示蘊含（implies），這裡表示"如果 a ≠ 0，則..."
-- 命題：`a ≠ 0 → a * a⁻¹ = 1` 表示非零數都有乘法逆元
-- 在 Lean 中，實數 ℝ 是域（Field），可以直接使用類型類實例的 `mul_inv_cancel`
-- 語法：透過類型類解析，Lean 會自動找到 Field 實例並應用 `mul_inv_cancel`
-- 注意：`a / a = 1` 等價於 `a * a⁻¹ = 1`，因為 `a / a = a * a⁻¹`

-- ============================================
-- 3. 分配律 (Distributivity)
-- ============================================

-- 公設 3：分配律 (Distributivity)
-- 左分配律：`a * (b + c) = a * b + a * c`
-- `mul_add` 定理實作左分配律

-- 右分配律：`(a + b) * c = a * c + b * c`
-- `add_mul` 定理實作右分配律


-- 對於任意實數 a，有 0 · a = 0
example (a : ℝ) : 0 * a = 0 := by
  calc
    0 * a
      = 0 * a + 0                   := by rw [add_zero]
    _ = 0 * a + (0 * a + - (0 * a)) := by rw [add_neg_cancel]
    _ = (0 * a + 0 * a) + - (0 * a) := by rw [add_assoc]
    _ = (0 + 0) * a + - (0 * a) := by rw [← add_mul]
    _ = 0 * a + - (0 * a) := by rw [add_zero]
    _ = 0 := by rw [add_neg_cancel]
/-
example (a : ℝ) : 0 * a = 0 := zero_mul a -- 後續使用 zero_mul 定理
-/


-- 對於任意實數 a，有 -a = (-1) · a
example (a : ℝ) : -a = (-1) * a := by
  have h : a + (-1) * a = 0 := by
    calc
      a + (-1) * a
        = 1 * a + (-1) * a := by rw [one_mul]
      _ = (1 + (-1)) * a := by rw [← add_mul]
      _ = 0 * a := by rw [add_neg_cancel]
      _ = 0 := by rw [zero_mul]
  have h2 : (-1) * a = -a := eq_neg_of_add_eq_zero_right h
  rw [eq_comm]
  exact h2
/-
example (a : ℝ) : -a = (-1) * a := neg_one_mul a  -- 後續使用 neg_one_mul 定理
-/


-- 對於任意實數 a，有 -(-a) = a
example (a : ℝ) : -(-a) = a := by
  have h : a + -a = 0 := add_neg_cancel a
  have h2 : a = -(-a) := eq_neg_of_add_eq_zero_left h
  rw [eq_comm]
  exact h2
/-
example (a : ℝ) : -(-a) = a := neg_neg a -- 後續使用 neg_neg 定理
-/

-- 對於任意實數 a，有 (-1) * (-1) = 1
example : (-1) * (-1) = 1 := by rw [neg_one_mul, neg_neg]


-- 對於任意實數 a，有 -(a - b) = b - a
example (a b : ℝ ) : -(a - b) = b - a := by
  calc
    -(a - b)
      = -(a + (-b)) := by rw [sub_eq_add_neg]
    _ = (-1) * (a + (-b)) := by rw [← neg_one_mul]
    _ = (-1) * a + (-1) * (-b) := by rw [mul_add]
    _ = (-1) * a + (-(-b)) := by rw [neg_one_mul (-b)]
    _ = (-1) * a + b := by rw [neg_neg]
    _ = -a + b := by rw [neg_one_mul]
    _ = b - a := by rw [add_comm, sub_eq_add_neg]
/-
example (a b : ℝ ) : -(a - b) = b - a := by rw [neg_sub] -- 後續使用 neg_sub 定理
-/


-- 對於任意實數 a，有 a * b = 0 → a = 0 ∨ b = 0
example (a b : ℝ) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  intro h
  by_cases h1 : a = 0
  · -- case a = 0
    exact Or.inl h1
  · -- case a ≠ 0
    right
    have h2 : b = 0 := by
      calc
        b = b * 1 := by rw [mul_one]
        _ = b * (a⁻¹ * a) := by rw [← inv_mul_cancel₀ h1]
        _ = (a⁻¹ * a) * b := by rw [mul_comm]
        _ = a⁻¹ * (a * b) := by rw [mul_assoc]
        _ = a⁻¹ * 0 := by rw [h]
        _ = 0 := by rw [mul_zero]
    exact h2
  intro h
  cases h with
  | inl ha =>
    rw [ha]
    rw [mul_comm, mul_zero]
  | inr hb =>
    rw [hb]
    rw [mul_zero]

/-
example (a b : ℝ) : a * b = 0 ↔ a = 0 ∨ b = 0 := mul_eq_zero -- 後續使用 mul_eq_zero 定理
-/


-- ============================================
-- 4. 序公理 (Order Axioms)
-- ============================================

-- 先寫課本上的 Postulate 2，再補充 Lean/Mathlib 常用版本。

-- Postulate 2. [ORDER AXIOMS]
-- There is a relation `<` on `ℝ × ℝ` that has the following properties:

-- (1) Trichotomy Property（三歧性）
-- 語法（課本）：給定 a, b ∈ ℝ，以下三者「恰有一個」成立：
--   `a < b`  或  `b < a`  或  `a = b`
-- Lean 中常用的三歧定理：
--   `lt_trichotomy a b : a < b ∨ a = b ∨ b < a`
example (a b : ℝ) : a < b ∨ a = b ∨ b < a := lt_trichotomy a b

-- (2) Transitive Property（傳遞性）
-- 語法（課本）：`a < b` 且 `b < c` 蘊含 `a < c`
-- Lean：`lt_trans h₁ h₂`
example (a b c : ℝ) (h₁ : a < b) (h₂ : b < c) : a < c := lt_trans h₁ h₂

-- (3) The Additive Property（加法保序）
-- 語法（課本）：`a < b` 且 `c ∈ ℝ` 蘊含 `a + c < b + c`
-- Lean：`add_lt_add_right h c`（或 `add_lt_add_left h c`）
example (a b c : ℝ) (h : a < b) : a + c < b + c := add_lt_add_right h c

-- (4) The Multiplicative Properties（乘法性質）
-- (4a) 若 `c > 0`，則 `a < b` 蘊含 `a*c < b*c`
-- Lean：`mul_lt_mul_of_pos_right h hc`
example (a b c : ℝ) (hc : 0 < c) (h : a < b) : a * c < b * c :=
  mul_lt_mul_of_pos_right h hc

-- (4b) 若 `c < 0`，則 `a < b` 蘊含 `b*c < a*c`（乘負數會翻轉不等號）
-- Lean：`mul_lt_mul_of_neg_right h hc`
example (a b c : ℝ) (hc : c < 0) (h : a < b) : b * c < a * c :=
  mul_lt_mul_of_neg_right h hc

-- 課本的符號約定（在 Lean 裡也成立，只是多半已經內建為 notation）
-- - `b > a` 表示 `a < b`（Lean 的 `b > a` 就是 `a < b`）
-- - `a ≤ b`、`a ≥ b` 是弱不等式（在 Lean 裡 `≤`/`≥` 本身就是基本關係）
-- - `a < b < c` 表示 `a < b` 且 `b < c`（在 Lean 裡通常寫成 `a < b ∧ b < c`）

-- ------------------------------------------------------------------------------------------------
-- 補充：常用的 `≤` 版本（寫證明時很常用）
-- - `le_rfl a : a ≤ a`（反身性）
-- - `le_trans h₁ h₂ : a ≤ c`（傳遞性）
-- - `add_le_add_right h c : a + c ≤ b + c`（加法保序）
-- - `mul_le_mul_of_nonneg_right h hc : a*c ≤ b*c`（右乘非負數保序）

-- 例：對於任意實數 a，有 a ≠ 0 → a² > 0（這裡用 a*a 代表 a²）
example (a : ℝ) : a ≠ 0 → a * a > 0 := by
  intro h
  have h1 : a < 0 ∨ a > 0 := ne_iff_lt_or_gt.mp h
  cases h1 with
  | inl h1 =>
    have : a * a > 0 * a := mul_lt_mul_of_neg_right h1 h1
    have a_mul_0 : 0 * a = 0 := zero_mul a
    rw [a_mul_0] at this
    exact this
  | inr h1 =>
    have : a * a > 0 * a := mul_lt_mul_of_pos_right h1 h1
    have a_mul_0 : 0 * a = 0 := zero_mul a
    rw [a_mul_0] at this
    exact this

/-
example (a : ℝ) : a ≠ 0 → a * a > 0 := by
  intro h
  have h1 : a < 0 ∨ a > 0 := ne_iff_lt_or_gt.mp h
  cases h1 with
  | inl h1 =>
    exact mul_pos_of_neg_of_neg h1 h1 -- 後續使用 mul_pos_of_neg_of_neg : a < 0 → b < 0 → a * b > 0 定理
  | inr h1 =>
    exact mul_pos h1 h1 -- 後續使用 mul_pos : a > 0 → b > 0 → a * b > 0 定理
-/

-- If a ∈ R, prove that 0 < a < 1 implies 0 < a² < a and a > 1 implies a² > a.
example (a : ℝ) : 0 < a ∧ a < 1 → 0 < a * a ∧ a * a < a := by
  intro h
  rcases h with ⟨h_pos, h_lt_1⟩
  constructor
  · exact mul_pos h_pos h_pos
  · have h_a_a : a * a < 1 * a := mul_lt_mul_of_pos_right h_lt_1 h_pos
    have h_a : 1 * a = a := one_mul a
    rw [h_a] at h_a_a
    exact h_a_a

example (a : ℝ) : a > 1 → a * a > a := by
  intro h
  have h_pos : 0 < a := lt_trans zero_lt_one h
  have h_a_a : a * a > 1 * a := mul_lt_mul_of_pos_right h h_pos
  have h_a : 1 * a = a := one_mul a
  rw [h_a] at h_a_a
  exact h_a_a

-- ============================================
-- 1.4 Definition：絕對值 (Absolute Value) 的語法對應
-- ============================================

-- 課本定義（分段）：
--   |a| := { a    if a ≥ 0
--          { -a   if a < 0

-- 但在 Mathlib 裡，絕對值已經內建好了：
-- - 函數名：`abs`
-- - 記號：`|a|`（notation）

-- （在 Lean 裡 `|a|` 就是 `abs a` 的 notation）
example (a : ℝ) : |a| = abs a := rfl

-- 例：對應課本分段的兩個 case（這就是課本定義在 Mathlib 的常用改寫定理）
-- - 若 `0 ≤ a`，則 `|a| = a`：`abs_of_nonneg`
-- - 若 `a < 0`，則 `|a| = -a`：`abs_of_neg`
example (a : ℝ) (h : 0 ≤ a) : |a| = a := abs_of_nonneg h

example (a : ℝ) (h : a < 0) : |a| = -a := abs_of_neg h

--1.5 Remark. The absolute value is multiplicative; that is, |ab| = |a| |b| for all a, b ∈ R.
example (a b : ℝ) : |a * b| = |a| * |b| := by
  by_cases ha : 0 ≤ a
  · -- case 1: 0 ≤ a
    by_cases hb : 0 ≤ b
    · -- case 1.1: 0 ≤ a ∧ 0 ≤ b
      have hab : 0 ≤ a * b := mul_nonneg ha hb
      calc
        |a * b| = a * b := abs_of_nonneg hab
        _ = |a| * |b| := by
          rw [abs_of_nonneg ha, abs_of_nonneg hb]
    · -- case 1.2: 0 ≤ a ∧ b < 0
      have hb' : b < 0 := lt_of_not_ge hb
      have hab : a * b ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hb')
      calc
        |a * b| = -(a * b) := abs_of_nonpos hab
        _ = a * (-b) := by
          rw [mul_neg]
        _ = |a| * |b| := by
          rw [abs_of_nonneg ha, abs_of_neg hb']
  · -- case 2: a < 0
    have ha' : a < 0 := lt_of_not_ge ha
    by_cases hb : 0 ≤ b
    · -- case 2.1: a < 0 ∧ 0 ≤ b
      have hab : a * b ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha') hb
      calc
        |a * b| = -(a * b) := abs_of_nonpos hab
        _ = (-a) * b := by
          rw [neg_mul]
        _ = |a| * |b| := by
          rw [abs_of_neg ha', abs_of_nonneg hb]
    · -- case 2.2: a < 0 ∧ b < 0
      have hb' : b < 0 := lt_of_not_ge hb
      have hab : a * b > 0 :=
        mul_pos_of_neg_of_neg ha' hb'
      calc
        |a * b| = a * b := abs_of_pos hab
        _ = (-a) * (-b) := by
          rw [neg_mul_neg]
        _ = |a| * |b| := by
          rw [abs_of_neg ha', abs_of_neg hb']

/-
example (a b : ℝ) : |a * b| = |a| * |b| := abs_mul a b -- 後續使用 abs_mul 定理
-/

--1.6 Theorem. [FUNDAMENTAL THEOREM OF ABSOLUTE VALUES].
--Let a ∈ R and M ≥ 0. Then |a| ≤ M if and only if −M ≤ a ≤ M.
example (a : ℝ) (M : ℝ) (hM : M ≥ 0) : |a| ≤ M ↔ -M ≤ a ∧ a ≤ M := by
  constructor
  intro h
  by_cases ha : 0 ≤ a
  · -- case 1: 0 ≤ a
    have h_a : |a| = a := abs_of_nonneg ha
    constructor
    · have a_ge_negM : -M ≤ a := by linarith
      exact a_ge_negM
    · have a_le_M : a ≤ M := by
        rw [h_a] at h
        exact h
      exact a_le_M
  · -- case 2: a < 0
    have ha' : a < 0 := lt_of_not_ge ha
    have h_a : |a| = -a := abs_of_neg ha'
    constructor
    · rw [h_a] at h
      have a_ge_negM : -M ≤ a := by
         have neg1_le_0 : (-1 : ℝ) ≤ 0 := by norm_num
         have h1 : M ≥ -a := by
            exact h
         have h2 : M * (-1) ≤ (-a) * (-1) := mul_le_mul_of_nonpos_right h1 neg1_le_0
         have h3 : -M = M * (-1) := by rw [mul_neg_one]
         have h4 : (-a) * (-1) = a := by rw [mul_neg_one, neg_neg]
         rw [← h3, h4] at h2
         exact h2
      exact a_ge_negM
    · have a_le_M : a ≤ M := by linarith
      exact a_le_M
  intro h
  rcases h with ⟨h_neg, h_pos⟩
  by_cases ha : 0 ≤ a
  · -- case 1: 0 ≤ a
    have h_a : |a| = a := abs_of_nonneg ha
    rw [h_a]
    exact h_pos
  · -- case 2: a < 0
    have ha' : a < 0 := lt_of_not_ge ha
    have h_a : |a| = -a := abs_of_neg ha'
    rw [h_a]
    have : -a ≤ M := by
      have neg1_le_0 : (-1 : ℝ) ≤ 0 := by norm_num
      have h1 : (-M) * (-1) ≥ a * (-1) := mul_le_mul_of_nonpos_right h_neg neg1_le_0
      have h2 : (-M) * (-1) = M := by rw [mul_neg_one, neg_neg]
      have h3 : a * (-1) = -a := by rw [mul_neg_one]
      rw [h2, h3] at h1
      exact h1
    exact this

/-
`neg_nonneg` : -a ≥ 0 ↔ a ≤ 0
`neg_le_neg` : a ≤ b → -b ≤ -a
example (a : ℝ) (M : ℝ) : |a| ≤ M ↔ -M ≤ a ∧ a ≤ M := by
  exact abs_le -- 後續使用 abs_le 定理
example (a : ℝ) (M : ℝ) : |a| < M ↔ -M < a ∧ a < M := by
  exact abs_lt  -- 後續使用 abs_lt 定理
-/


-- 1.7 Theorem. The absolute value satisfies the following three properties.
--(i) [Positive Definite] For all a ∈ R, |a| ≥ 0 with |a| = 0 if and only if a = 0.
example (a : ℝ) : 0 ≤ |a| := abs_nonneg a -- 後續使用 abs_nonneg 定理
example (a : ℝ) : |a| = 0 ↔ a = 0 := abs_eq_zero
-- (ii) [Symmetric] For all a, b ∈ R, |a − b| = |b − a|.
example (a b : ℝ) : |a - b| = |b - a| := abs_sub_comm a b
-- (iii) [Triangle Inequalities] For all a, b ∈ R, |a + b| ≤ |a| + |b| and ||a| − |b|| ≤ |a − b|.
example (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b
example (a b : ℝ) : abs (|a| - |b|) ≤ |a - b| := abs_abs_sub_abs_le_abs_sub a b

-- 1.8 EXAMPLE. Prove that if −2 < x < 1, then |x² − x| < 6.
example (x : ℝ) : -2 < x ∧ x < 1 → |x^2 - x| < 6 := by
  intro h
  rcases h with ⟨hx1, hx2⟩

  -- |x| < 2
  have hx_abs : |x| < 2 := by
    have hx_lt_2 : x < 2 := lt_trans hx2 (by norm_num)
    exact abs_lt.mpr ⟨hx1, hx_lt_2⟩

  -- |x^2| < 4
  have hx2_abs : |x^2| < 4 := by
    have 2 = |2|
    have : |x|^2 < 2^2 := by
      exact sq_lt_sq.mpr ⟨hx_nonneg x, hx_abs⟩
