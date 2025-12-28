
# Theorem and Proofs on Equilibrium Existence in a Disclosure Model

This file presents definitions and two theorems formalized in Lean 4, translated into mathematical statements with proofs in Markdown using LaTeX.

## Definitions

Let $f : \mathbb{R} \to \mathbb{R}$ be a function interpreted as a probability density function on $[0, \bar{x}]$, where $\bar{x} > 0$.

The **conditional expectation** of the random variable conditional on being in $[0, x]$ is defined as:

$$
E[\tilde{x} \mid \tilde{x} \leq x] =
\begin{cases}
0 & \text{if } \int_0^x f(t) \, dt = 0, \\
\frac{\int_0^x t f(t) \, dt}{\int_0^x f(t) \, dt} & otherwise.
\end{cases}
$$

Formally:

$$
\mathit{conditional\_expectation}(f)(x) =
\begin{cases}
0 & \text{if } \int_0^x f(t) \, dt = 0, \\
\frac{\int_0^x t f(t) \, dt}{\int_0^x f(t) \, dt} & otherwise.
\end{cases}
$$

The unconditional expected value is

$$
\mu = \int_0^{\bar{x}} x f(x) \, dx.
$$

The **key equation** for a candidate disclosure threshold $x$ is

$$
p \mu + (1 - p) \cdot E[\tilde{x} \mid \tilde{x} \leq x] = x,
$$

where $p \in (0,1)$ is a parameter.

## Distribution Assumptions

We assume the following structure holds:

- $\bar{x} > 0$
- $f(x) \geq 0$ for all $x$
- $f$ is continuous on $[0, \bar{x}]$
- $f$ is interval-integrable on $[0, \bar{x}]$
- $\int_0^{\bar{x}} f(x) \, dx = 1$
- $f(x) > 0$ for all $x \in (0, \bar{x})$
- The conditional expectation function is continuous on $[0, \bar{x}]$

## Theorem 1 Part One: Existence of Non-Degenerate Equilibrium

**Theorem.** Let $p \in (0,1)$, $\mu > 0$, $\mu < \bar{x}$, and let the distribution assumptions hold with total mass $\int_0^{\bar{x}} f(x) \, dx = 1$ and $\mu = \int_0^{\bar{x}} x f(x) \, dx$.  
Then there exists $x \in (0, \bar{x})$ such that

$$
p \mu + (1 - p) \cdot E[\tilde{x} \mid \tilde{x} \leq x] = x.
$$

**Proof.**

Define the function

$$
g(x) = p \mu + (1 - p) \cdot E[\tilde{x} \mid \tilde{x} \leq x] - x.
$$

By the assumptions, $E[\tilde{x} \mid \tilde{x} \leq x]$ is continuous on $[0, \bar{x}]$, so $g$ is continuous on the compact interval $[0, \bar{x}]$.

Evaluate at the endpoints:

- At $x = 0$:  
  $$
  E[\tilde{x} \mid \tilde{x} \leq 0] = 0 \quad \Rightarrow \quad g(0) = p \mu + (1 - p) \cdot 0 - 0 = p \mu > 0,
  $$
  since $p > 0$ and $\mu > 0$.

- At $x = \bar{x}$:  
  $$
  E[\tilde{x} \mid \tilde{x} \leq \bar{x}] = \mu \quad \Rightarrow \quad g(\bar{x}) = p \mu + (1 - p) \mu - \bar{x} = \mu - \bar{x} < 0,
  $$
  since $\mu < \bar{x}$.

Thus, $g(0) > 0$ and $g(\bar{x}) < 0$. By the Intermediate Value Theorem on the closed interval $[0, \bar{x}]$, there exists $x \in [0, \bar{x}]$ such that $g(x) = 0$.

Moreover, this root cannot be at the endpoints:

- If $x = 0$, then $g(0) = p \mu > 0 \neq 0$.
- If $x = \bar{x}$, then $g(\bar{x}) = \mu - \bar{x} < 0 \neq 0$.

Hence, the root satisfies $0 < x < \bar{x}$, and $g(x) = 0$ is equivalent to the key equation. ∎

## Theorem 1 Part Two: No Complete Disclosure Equilibrium ($x = 0$)

**Theorem.** Under the assumptions $p \in (0,1)$ and $\mu > 0$, there is no equilibrium with full disclosure threshold $x = 0$. That is,

$$
\neg \bigl( p \mu + (1 - p) \cdot E[\tilde{x} \mid \tilde{x} \leq 0] = 0 \bigr).
$$

**Proof.**

Suppose for contradiction that the key equation holds at $x = 0$:

$$
p \mu + (1 - p) \cdot E[\tilde{x} \mid \tilde{x} \leq 0] = 0.
$$

By definition, $E[\tilde{x} \mid \tilde{x} \leq 0] = 0$, so

$$
p \mu + (1 - p) \cdot 0 = 0 \quad \Rightarrow \quad p \mu = 0.
$$

However, $p > 0$ and $\mu > 0$ imply $p \mu > 0$, a contradiction.

Thus, $x = 0$ cannot satisfy the key equation. ∎
