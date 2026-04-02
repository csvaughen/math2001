# Study Guide: Section 2.1 — Intermediate Steps
## *The Mechanics of Proof* by Heather Macbeth

---

## The Big Idea

Chapter 1 proofs were **single-step calculations** — one `calc` block from hypothesis to goal. Section 2.1 introduces **multi-step proofs**: you establish *intermediate facts* along the way, give them names, and use them later. This is how real mathematical proof works.

The key Lean keyword is **`have`** — it lets you claim and prove a fact mid-proof, then refer to it by name in subsequent steps.

---

## Core Concepts

### 1. The `have` Tactic

**Purpose:** Establish an intermediate fact and give it a name.

**Syntax patterns:**

```lean
-- Pattern A: Prove an intermediate fact with a tactic
have hb : b = 1 := by addarith [h2]

-- Pattern B: Prove an intermediate fact with a calc block
have h3 :=
calc
  m + 3 ≤ 2 * n - 1 := by rel [h1]
  _ ≤ 2 * 5 - 1 := by rel [h2]
  _ = 9 := by numbers

-- Pattern C: State a fact without proof (creates a new goal)
have hp' : -3 ≤ p ∧ p ≤ 3
```

**What happens in the Infoview:** After a `have`, your new named fact appears in the hypothesis list, available for all subsequent steps.

### 2. The Lean Infoview

This is your **proof dashboard**. It shows:

- **Variables** (e.g., `a b : ℝ`)
- **Hypotheses** — named facts you know (e.g., `h1 : a - 5 * b = 4`)
- **Goal** — what you still need to prove (after the `⊢` symbol)

As you move your cursor through the proof, the Infoview updates live. When you see **"No goals"**, the proof is complete.

**Mental model:** Think of the Infoview as a running ledger. Each `have` deposits a new fact into your account. Each proof step withdraws from it.

### 3. The `cancel` Tactic

**Purpose:** Cancel a common factor from both sides of an equation or inequality.

**Key requirement:** The factor being cancelled must be known to be **nonzero** (for equations) or **nonnegative** (for inequalities involving squares).

**Examples:**

```lean
-- If h3 : t * t = 3 * t  and  t ≥ 1 (so t ≠ 0):
cancel t at h3
-- Now h3 : t = 3

-- If h3 : a ^ 2 ≥ 1 ^ 2  and  a ≥ 0:
cancel 2 at h3
-- Now h3 : a ≥ 1
```

**Watch out:** Lean silently checks the nonzero/nonnegative condition. If it can't verify it from your hypotheses, the tactic fails.

---

## Tactic Reference for Section 2.1

| Tactic | What It Does | When to Use |
|---|---|---|
| `have h : P := by ...` | Proves and names an intermediate fact | When you need a stepping-stone result |
| `calc` | Chain of equalities/inequalities | Main workhorse for computational proofs |
| `ring` | Proves algebraic identities | Pure algebra with no hypotheses needed |
| `rw [h]` | Rewrites using hypothesis `h` | Substituting a known equality |
| `addarith [h]` | Adds/subtracts from hypothesis | "Obviously" follows by arithmetic on `h` |
| `rel [h]` | Monotonicity reasoning for inequalities | Plugging an inequality into a larger expression |
| `numbers` | Verifies numerical facts | Checking concrete arithmetic (e.g., `2/3 < 1`) |
| `extra` | Proves "obvious" positivity/nonnegativity | When squares are nonneg, sums of positive terms, etc. |
| `cancel x at h` | Cancels common factor in `h` | When both sides share a nonzero factor |

---

## Proof Strategy Flowchart

When you see a Section 2.1–style problem, think:

1. **What do I ultimately need to show?** (Read the goal.)
2. **Can I get there in one calculation?** If yes, do a single `calc` block (Chapter 1 style).
3. **If not, what intermediate fact would help?** This is the creative step.
   - Can I solve for one variable first, then substitute?
   - Can I establish an inequality that simplifies the final step?
   - Can I rewrite the goal into a form where `cancel` applies?
4. **Prove the intermediate fact** using `have`.
5. **Use it** in your final `calc` block or tactic call.

---

## Worked Examples with Commentary

### Example A: Solving a system by substitution

**Problem:** Given `a - 5b = 4` and `b + 2 = 3`, show `a = 9`.

**Strategy:** Solve for `b` first (it's easy), then substitute.

```lean
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]       -- intermediate step
  calc
    a = a - 5 * b + 5 * b := by ring         -- algebraic rearrangement
    _ = 4 + 5 * 1 := by rw [h1, hb]          -- substitute known facts
    _ = 9 := by ring                          -- simplify
```

**Infoview evolution:**
- Before `have`: hypotheses are `h1` and `h2`, goal is `a = 9`
- After `have`: `hb : b = 1` is added to hypotheses
- After `calc`: "No goals"

### Example B: Chaining inequalities

**Problem:** Given `m + 3 ≤ 2n - 1` and `n ≤ 5`, show `m ≤ 6`.

**Strategy:** First bound `m + 3`, then subtract 3.

```lean
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]                               -- m + 3 ≤ 9 implies m ≤ 6
```

**Key insight:** The `calc` block establishes `h3 : m + 3 ≤ 9`. Then `addarith` finishes by subtracting 3 from both sides — that's "obvious enough" not to need a full calculation.

### Example C: Using `cancel`

**Problem:** Given `t² = 3t` and `t ≥ 1`, show `t ≥ 2`.

**Strategy:** Rewrite as `t · t = 3t`, cancel `t`, get `t = 3`.

```lean
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3          -- h3 becomes: t = 3 (valid because t ≥ 1 > 0)
  addarith [h3]           -- t = 3 ≥ 2
```

**Why can we cancel?** Because `t ≥ 1` means `t > 0`, so `t ≠ 0`. Lean checks this automatically.

### Example D: Cancelling with squares

**Problem:** Given `a² = b² + 1` and `a ≥ 0`, show `a ≥ 1`.

```lean
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra          -- b² ≥ 0, so b² + 1 ≥ 1
    _ = 1 ^ 2 := by ring
  cancel 2 at h3               -- a² ≥ 1² with a ≥ 0 gives a ≥ 1
```

**Note:** `cancel 2 at h3` cancels the *exponent* 2. This works because `a ≥ 0` — you can't take square roots of both sides of an inequality without knowing the sign.

---

## Common Mistakes

1. **Forgetting to name your intermediate fact.** Every `have` needs a name (like `hb`, `h3`) — you'll reference it later.

2. **Using `cancel` without a nonzero guarantee.** If Lean can't verify the factor is nonzero from your hypotheses, the tactic fails. Check: do you have `t ≥ 1`, or `t > 0`, or something that implies nonzero?

3. **Trying to do too much in one step.** If `addarith` or `ring` can't close a gap, break it into smaller steps with `have`.

4. **Wrong justification tactic.** Quick guide:
   - Pure algebra (no hypotheses needed) → `ring`
   - Plugging in a known equality → `rw [h]`
   - Arithmetic on a hypothesis → `addarith [h]`
   - Inequality monotonicity → `rel [h]`
   - Concrete numbers → `numbers`
   - Squares are nonneg, sums of positive things → `extra`

5. **Confusing `rw` and `addarith`.** `rw` does *exact substitution* of an equality. `addarith` does *arithmetic reasoning* (add/subtract from both sides). If your hypothesis is `h : b = 1`, use `rw [h]` to replace `b` with `1`. If your hypothesis is `h : b + 2 = 3`, use `addarith [h]` to conclude `b = 1`.

---

## Practice Problems

### Warm-Up (direct application of techniques)

**Problem 1.** Let `x` and `y` be real numbers with `x + y = 10` and `x - y = 4`. Show that `x = 7`.

*Hint:* Establish `2 * x = 14` as an intermediate step by adding the two hypotheses.

**Problem 2.** Let `a` be an integer with `a + 5 ≤ 3` and `2a ≥ -6`. Show that `a = -3`.

*Hint:* Use `addarith` to extract `a ≤ -2` and `a ≥ -3`, then apply `le_antisymm`.

**Problem 3.** Let `p` be a real number with `p² = 4p` and `p ≥ 2`. Show that `p = 4`.

*Hint:* Rewrite as `p * p = 4 * p`, then `cancel p`.

### Medium (requires choosing a good intermediate step)

**Problem 4.** Let `r` and `s` be rationals with `r + 2s ≤ 5` and `s ≥ 1`. Show that `r ≤ 3`.

*Hint:* Use `have` with a `calc` block to show `r + 2 ≤ r + 2s ≤ 5`.

**Problem 5.** Let `a` and `b` be reals with `-b ≤ a` and `a ≤ b`. Show that `a² ≤ b²`.

*Hint:* Establish `0 ≤ b + a` and `0 ≤ b - a` as intermediate facts, then show `a² ≤ a² + (b+a)(b-a) = b²`.

**Problem 6.** Let `a` and `b` be reals with `a ≤ b`. Show that `a³ ≤ b³`.

*Hint:* Establish `0 ≤ b - a`, then show `a³ ≤ a³ + (b-a)[(b-a)² + 3(b+a)²]/4 = b³`. The expression `(b-a)[(b-a)² + 3(b+a)²]/4` is nonneg because it's a product of nonneg terms.

### Challenge (from the textbook exercises)

**Problem 7.** Let `x` be a rational with `x² = 4` and `1 < x`. Show that `x = 2`.

*Hint:* Show `x(x+2) = 2(x+2)`, then cancel `x + 2` (why is it nonzero?).

**Problem 8.** Let `n` be an integer with `n² + 4 = 4n`. Show that `n = 2`.

*Hint:* Show `(n-2)² = 0`, cancel the square to get `n - 2 = 0`.

**Problem 9.** Let `x` and `y` be rationals with `xy = 1` and `x ≥ 1`. Show that `y ≤ 1`.

*Hint:* First establish `0 < xy` (it equals 1), then use cancellation reasoning and a `calc` block.

---

## Key Takeaways

- **`have` is your new best friend.** It's the difference between Chapter 1 proofs (one shot) and real mathematical reasoning (build up facts, then combine them).

- **The Infoview is your co-pilot.** Always watch it. It tells you exactly what you know and what you still need to prove.

- **`cancel` is powerful but conditional.** It requires nonzero/nonneg verification — make sure your hypotheses support it.

- **Choosing good intermediate steps is the art.** The mechanics (which tactic to use) are learnable; the strategy (what to prove first) takes practice.
