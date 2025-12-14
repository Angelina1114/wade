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
