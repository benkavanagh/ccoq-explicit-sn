module NatProperties where

open import Data.Empty
open import Data.Nat
open import Relation.Binary.PropositionalEquality

m≤sm : ∀ m → m ≤ suc m
m≤sm zero = z≤n
m≤sm (suc m) = s≤s (m≤sm m)

≤-refl : ∀ m → m ≤ m
≤-refl zero = z≤n
≤-refl (suc m) = s≤s (≤-refl m)

<-irrefl : ∀ {n} (pr : n < n) → ⊥
<-irrefl (s≤s pr) = <-irrefl pr

≤-trans : ∀ {m n p} (pr₁ : m ≤ n) (pr₂ : n ≤ p) → m ≤ p
≤-trans z≤n pr₂ = z≤n
≤-trans (s≤s pr₁) (s≤s pr₂) = s≤s (≤-trans pr₁ pr₂)

<-inject-≤ : ∀ {m n} (pr : m < n) → m ≤ n
<-inject-≤ pr = ≤-trans (m≤sm _) pr

≤<-compat : ∀ {m n p} (pr₁ : m ≤ n) (pr₂ : n < p) → m < p
≤<-compat pr₁ pr₂ = ≤-trans (s≤s pr₁) pr₂

<≤-compat : ∀ {m n p} (pr₁ : m < n) (pr₂ : n ≤ p) → m < p
<≤-compat pr₁ pr₂ = ≤-trans pr₁ pr₂

<-trans : ∀ {m n p} (pr₁ : m < n) (pr₂ : n < p) → m < p
<-trans pr₁ pr₂ = <≤-compat pr₁ (<-inject-≤ pr₂)

m≤m⊔n : ∀ m n → m ≤ m ⊔ n
m≤m⊔n zero n = z≤n
m≤m⊔n (suc m) zero = ≤-refl _
m≤m⊔n (suc m) (suc n) = s≤s (m≤m⊔n m n)

m≤n⊔m : ∀ m n → m ≤ n ⊔ m
m≤n⊔m zero n = z≤n
m≤n⊔m (suc m) zero = s≤s (m≤n⊔m m zero)
m≤n⊔m (suc m) (suc n) = s≤s (m≤n⊔m m n)