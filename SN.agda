module SN where

open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Bool hiding  (_≟_)  -- true/false,  T predicate
open import Data.Nat hiding (_≥_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality 
import Relation.Binary.HeterogeneousEquality as H
import Level as Lvl

open import Closures
open import NatProperties
open import PT
open import Kripke

calculus : Kripke
calculus = kripke Context _≥_ ≥-isPreorder lemma₇ (λ Γ → Γ ⊢ ♭)



module KS = KSem calculus
open KS

_⊢⇑_ : (Γ : Context)(A : Type) → Set
Γ ⊢⇑ A = ∀ {Δ} (c : Δ ≥ Γ) → Δ ⊢ A

mutual

  -- idea: 
  -- if M ∈ Γ ⊢ A₁ → ... → An → ♭  then
  -- reify (⟦M⟧) ≝ λ(z₁ : A₁)...λ(zn : An).(⟦M⟧ val(z₁)...val(zn)
  -- where ⟦M⟧ val(z₁)...val(zn) is a proof tree of type ♭ and z₁ ... zn are fresh names
  --  and if x is a variable of type A₁ → ...Ak → B, then
  --  val(x) = Λ([v₁]...Λ([vk](x reify(v₁) ... reify(vn))  (where [v₁] is simplified abstraction of (c, v) where
  --       c is a world extension w' ≥ w, v is an element of w' ⊩ Ai. Essentially, the kripke structure
  --       intelligently deals with reindexing of variables. Moves information from one world to a world where 
  --       we know more. 
  -- Example: 
  --   M ∈ ε ⊢ ((♭ → ♭) → ♭) → (♭ → ♭) → ♭  = λ [x : ((♭ → ♭) → ♭)]. λ [y : (♭ → ♭)]. x ⋆ y
  --   reify(⟦M⟧) = λ(z₁ : (♭ → ♭) → ♭). λ(z₂ : ♭ → ♭). (⟦M⟧ val(z₁) val(z₂))
  --                   = λ(z₁ : (♭ → ♭) → ♭). λ(z₂ : ♭ → ♭). z₁ (λ (z₃ : ♭). (z₂ z₃)    : by (1)

  --  (1)  ⟦M⟧ val(z₁) val(z₂) = ⟦x y⟧{x = val(z₁), y = val(z₂)}
  --                                    = app(val(z₁), val(z₂))
  --                                    = app(Λ([v](z₁ reify(v))), val(z₂))
  --                                    = z₁ (reify (val(z₂)))    
  --                                    = z₁ (λ (z₃ : ♭). (z₂ z₃)      : by (2)
  --  (2)   reify (val(z₂)) has type ♭ → ♭ so
  --         reify (val(z₂)) = λ (z₃ : ♭). app(val(z₂), val(z₃))
  --                             = λ (z₃ : ♭). app(Λ([v](z₂ reify(v))),  z₃)
  --                             = λ (z₃ : ♭). (z₂ reify(z₃))
  --                             = λ (z₃ : ♭). (z₂ z₃)

  -- map value of term kripke model to well typed term.
  reify : ∀ Γ A (u : Γ ⊩ A) → Γ ⊢ A
  reify Γ ♭ u = u P.refl
  reify Γ (A ⇒ B) u = ∶λ (fresh Γ) # (isfresh Γ)
                                  ⇨ (reify (Γ ∙[ fresh Γ ∶ A ]⊣ isfresh Γ) 
                                               B
                                               (u lemma₅ (val (Γ ∙[ fresh Γ ∶ A ]⊣ isfresh Γ)      -- semantic application of ⟦ M ⟧  i.e. (app ⟦M⟧ (val (fresh Γ)))
                                                                       A 
                                                                      (λ {Δ} (c : Δ ≥ _) → [ _ ∋ fresh Γ ↳ lemma₂ c here! ]))))

  -- map upward-closed family of (well-typed) terms to value in kripke term model
  --   Intuitively val intuitively takes a variable and produces  proof tree of the form of a variable applied to zero or
  --   whose values will be reified semantic values.  
  --   Observations:
  --      1. these look a lot like neutral values. How can I make this more precise?
  --      2. this function looks very underspecified. These upward closed familes could be arbitrary but they almost 
  --          certainly are not. How can I make this more precise? 
  val : ∀ Γ A (f : Γ ⊢⇑ A) → Γ ⊩ A
  val Γ ♭ f = f
  val Γ (A ⇒ B) f = λ {Δ} (c : Δ ≥ Γ) (a : Δ ⊩ A) →  
                               val Δ B (λ {Ε} (c' : Ε ≥ Δ) → f (P.trans c' c) ⋆ (reify Ε A ↑[ c' , A ]⟨ a ⟩))

--- END OF mutual decl for reify/val


-- what does valEq below say? 
-- The type (t : ∀ {Δ} (pr : Δ ≥ Γ) → Δ ⊢ A) needs a name.  I use  'upward closed familiy of terms' for now
-- Is this a family of proof trees 'above Γ' which designate the same term? 
-- essentially this is the idea, even if the straightforward constructive reading is different
-- i.e. for every environment Δ that contains Γ, a well typed term in Δ.

-- OK. two extensionally identical/equal upward-closed family of terms yield Eq kripke values. 
valEq : ∀ {Γ} A {f₁ f₂ : Γ ⊢⇑ A} (h : ∀ {Δ} (c : Δ ≥ Γ) → f₁ c ≡ f₂ c) →
        Eq⟨ Γ ⊩ A ⟩[ val Γ A f₁ , val Γ A f₂ ]
valEq ♭ h = h
valEq {Γ} (A ⇒ B) h =
  λ {Δ} (c : Δ ≥ Γ) {v : Δ ⊩ A} uv → valEq B (λ {Ε} (c' : Ε ≥ Δ) → cong (λ M → M ⋆ reify Ε A ↑[ c' , A ]⟨ v ⟩)
    (h (lemma₁ (λ {x} {A₁} occ → lemma₂ c' (lemma₂ c occ)))))


-- lifting result of val over contexts same as taking value at higher world 
--    (with appropriately constructed upward closed family of terms)
val↑ : ∀ {Γ} A {Δ} (c : Δ ≥ Γ) {f : Γ ⊢⇑ A} →
       Eq⟨ Δ ⊩ A ⟩[ ↑[ c , A ]⟨ val Γ A f ⟩ , val Δ A (λ {Ε} (c' : Ε ≥ Δ) → f (P.trans c' c)) ]
val↑ ♭ c = λ _ → refl
val↑ {Γ} (A ⇒ B) {Δ} c {f} =
  λ {Δ'} (c' : Δ' ≥ Δ) {v : Δ' ⊩ A} uv → valEq B (λ {Ε} c' → cong (λ t → f t ⋆ reify Ε A ↑[ c' , A ]⟨ v ⟩)
  (lemma₇ _ _))

mutual

  -- Equal semantic values reify to elements in the same equivalence class of terms.  (simple induction on type)
  theorem₁ : ∀ {Γ} A {u v} (eq : Eq⟨ Γ ⊩ A ⟩[ u , v ]) → reify Γ A u ≡ reify Γ A v
  theorem₁ ♭ eq = eq _
  theorem₁ {Γ} (A ⇒ B) eq = cong (∶λ_#_⇨_ (fresh Γ)(isfresh Γ)) (theorem₁ B (eq lemma₅ (valUni A)))

  -- reflection/values of upward closed family of terms is a uniform value.   (What does this mean?)
  valUni : ∀ {Γ} A {f : Γ ⊢⇑ A} → Uni⟨ Γ ⊩ A ⟩ val Γ A f
  valUni ♭ = tt
  valUni (A ⇒ B) {f} =
    (λ {Δ} inc {a} uni → valUni B) ,
    (λ {Δ} inc {v₁} {v₂} uni₁ uni₂ eq →
      valEq B (λ {Ε} pr → cong (_⋆_ (f (P.trans pr inc))) (theorem₁ A (Eq-cong-↑ A pr eq)))) ,
    (λ {Δ} {Ε} c₁ c₂ c₃ {v} uni → Eq-trans B (val↑ B c₂)
      (valEq B (λ {Φ} pr → cong₂ (λ inc t → f inc ⋆ t) (lemma₇ _ _)
               (theorem₁ A (Eq-sym A (Eq↑↑ A v _ _ _))))))

infix 10 idᵉ_

-- default 'identity' term model environment
idᵉ_ : (Γ : Context) → Γ ⊩ᵉ Γ
idᵉ ε = tt
idᵉ Γ ∙[ x ∶ A ]⊣ f =
  ↑ᵉ[ lemma₅ , Γ ]⟨ idᵉ Γ ⟩ ,
  val _ A (λ {Δ} inc → [ Δ ∋ x ↳ lemma₂ inc here! ])

idᵉ↑ : ∀ {Δ Γ} (c : Δ ≥ Γ) → Δ ⊩ᵉ Γ
idᵉ↑ {Δ} {Γ} c = ↑ᵉ[ c , Γ ]⟨ idᵉ Γ ⟩

-- prove uniformity of idᵉ  (required for theorem₂)
Uni-idᵉ : ∀ {Γ} → Uni⟨ Γ ⊩ᵉ Γ ⟩ (idᵉ Γ)
Uni-idᵉ {ε} = tt
Uni-idᵉ {Γ ∙[ x ∶ A ]⊣ f} = (Uniᵉ↑ Γ lemma₅ (Uni-idᵉ {Γ}) , valUni A )

-- normal form = reify ∘ eval
nf : ∀ {Γ A} (M : Γ ⊢ A) → Γ ⊢ A
nf {Γ} {A} M = reify Γ A (⟦ M ⟧t (idᵉ Γ))

corollary₁ : ∀ {Γ A} {M N : Γ ⊢ A} (eq : Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idᵉ Γ) , ⟦ N ⟧t (idᵉ Γ) ]) → nf M ≡ nf N
corollary₁ {Γ} {A} eq = theorem₁ {Γ} A eq -- theorem₁ _ eq


-- *******  Completeness for equational theory.  i.e. proper completeness  *************
-- *********      Goal:  Eq(⟦M⟧idᵉ, ⟦N⟧idᵉ)  implies   M ≅ N                    ******************
-- use Kripke relation CV
-- 
-- [Γ, A] M ∿ u  ≡ M, u are CV-related at type A in context Γ    (equiv to tait computability predicate)
-- [Δ, Γ]ε γ ∿ ρ   ≡  γ, ρ are CV-related at env Γ in context Δ

infix 10 [_,_]_∿_  [_,_]_∿ᵉ_

-- ∿ relates terms to values. 
-- t, T ∿-related at base/ground type if composition of t with proj subst π (c : Δ ≥ Γ) and T applied to 
--       c are convertible/equivalent terms
--       ∿ equivalent at function type if for all pr : Δ ≥ Γ.  (t  ⟨ π pr ⟩ ⋆ u) ↯ (T pr U) ,  for u, U. u ↯ U
[_,_]_∿_ : ∀ Γ A (M : Γ ⊢ A) (u : Γ ⊩ A) → Set
[ Γ , ♭ ] M ∿ u = ∀ {Δ} (c : Δ ≥ _) → Δ ⊢ ♭ ∋ M ⟨ π c ⟩ ≅ u c
[ Γ , A ⇒ B ] M ∿ u =
  ∀ {Δ} (c : Δ ≥ Γ) {N v} (cv : [ Δ , A ] N ∿ v) → [ Δ , B ] M ⟨ π c ⟩ ⋆ N ∿ u c v


-- ∿ᵉ relates term substitutions to value environments.
-- current definition seems a bit messy. Is there a reason? Why not use V2?
data [_,_]_∿ᵉ_ Δ : ∀ Γ (γ : Δ ⇛ Γ) (ρ : Δ ⊩ᵉ Γ) → Set where
  ε : ∀ {γ : Δ ⇛ ε} → [ Δ , ε ] γ ∿ᵉ tt
  ∙ : ∀ {Γ x A f} {γ : Δ ⇛ Γ ∙[ x ∶ A ]⊣ f}  
                 {ρ : Δ ⊩ᵉ Γ}  (πγρ : [ Δ ,  Γ ] π lemma₅ ⊙ γ ∿ᵉ ρ)  
                 {u : Δ ⊩ A}   (xu : [ Δ , A ] [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟨ γ ⟩ ∿ u) →
      [ Δ , Γ ∙[ x ∶ A ]⊣ f ] γ ∿ᵉ (ρ , u)

-- why not the following? todo test if all works this way. (V2)
--  ∙ : ∀ {Γ x A f} {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (γ∿ρ : [ Δ , Γ ] γ ∿ᵉ ρ)
--      (T : Δ ⊩ A) (t : Δ ⊢ A) (xu : [ Δ , A ]  t ∿ T) →
--      [ Δ , Γ ∙[ x ∶ A ]⊣ f ] (γ [ x ↦ t ]) ∿ᵉ (ρ , T)

-- βη-equivalent terms are ∿-related  to the same semantic values.  
-- (so if I can show that 
--       1. t is ∿-related  to ⟦t⟧  and 
--       2. two semantic values related to a single term are equal in model Eq...
--   then we should get proper soundness proof)
∿≡-cast : ∀ {Γ} A {M M' u} (eq : Γ ⊢ A ∋ M ≅ M') (cv : [ Γ , A ] M ∿ u) → [ Γ , A ] M' ∿ u
∿≡-cast ♭ {M} {M'} {u} eq cv = λ {Δ} c → ≡*-trans (≡*-cong cs₁ (≡*-sym eq)) (cv c)
∿≡-cast (A ⇒ B) {M} {M'} {u} eq cv = λ {Δ} c {N} {v} cvNv → ∿≡-cast B (≡*-cong (ca₁ ∘ cs₁) eq) (cv c cvNv)



-- βη-equivalent subsitutions are ∿ˢ-related to the same semantic environments.
∿≡ᵉ-cast : ∀ {Δ} Γ {γ₁ γ₂ ρ} (eq : Δ ⊢ Γ ∋ γ₁ ≅ˢ γ₂) (cv : [ Δ , Γ ] γ₁ ∿ᵉ ρ) → [ Δ , Γ ] γ₂ ∿ᵉ ρ
∿≡ᵉ-cast .ε eq ε = ε
∿≡ᵉ-cast (Γ ∙[ x ∶ A ]⊣ f) eq (∙ cv xu) =
   ∙ (∿≡ᵉ-cast Γ (≡*-cong c∘₂ eq) cv) (∿≡-cast A (≡*-cong cs₂ eq) xu)



-- ∿ relation lifts via context ordering (here lifting through c : Δ ≥ Γ)
∿↑ : ∀ {Γ Δ} A {M u} (c : Δ ≥ Γ) (cv : [ Γ , A ] M ∿ u) → [ Δ , A ] M ⟨ π c ⟩ ∿ ↑[ c , A ]⟨ u ⟩
∿↑ ♭ pr cv = λ {Ε} inc →
 ≡*-trans (lstep :s⊙ (lstep (cs₂ ∶⊙∶π) refl)) (cv _)
∿↑ (A ⇒ B) pr cv = λ {Δ} inc {u} {U} cvU →
  ∿≡-cast B (≡*-sym (lstep (ca₁ :s⊙) (lstep (ca₁ (cs₂ ∶⊙∶π)) refl))) (cv _ cvU)


-- (occ at explicit-subst) ∿-relates to (lookup at occ in semantic env) if explicit-subst and semantic env ∿ᵉ related.
∿-lookup : ∀ {Δ} Γ {x A} occ {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (cv : [ Δ , Γ ] γ ∿ᵉ ρ) →
            [ Δ , A ] [ Γ ∋ x ↳ occ ] ⟨ γ ⟩ ∿ lookup Γ ρ occ
∿-lookup .ε () ε
∿-lookup (Γ ∙[ x ∶ A ]⊣ f) here! (∙ cv xu) = xu
∿-lookup (Γ ∙[ x ∶ A ]⊣ f) {y} {B} (there .f pr) (∙ cv xu) =
  ∿≡-cast B (rstep :s⊙ (lstep (cs₁ :v₂) refl)) (∿-lookup Γ pr cv)



-- explicit-subst composition and semantic lifting preserve ∿ᵉ-relation
∿π : ∀ {Δ} Γ {Ε} (c : Ε ≥ Δ) {γ : Δ ⇛ Γ} {ρ} (cv : [ Δ , Γ ] γ ∿ᵉ ρ) →
      [ Ε , Γ ] γ ⊙ π c ∿ᵉ ↑ᵉ[ c , Γ ]⟨ ρ ⟩
∿π .ε c ε = ε
∿π (Γ ∙[ x ∶ A ]⊣ f) c (∙ cv xu) =
  ∙ (∿≡ᵉ-cast Γ (lstep ⊙-assoc refl) (∿π Γ c cv)) (∿≡-cast A (lstep :s⊙ refl) (∿↑ A c xu))

-- composing with projection  and  projecting semantic values preserve  ∿ᵉ -relation
∿πᵉ : ∀ {Δ} Γ {Ε} (c : Γ ≥ Ε) {γ : Δ ⇛ Γ} {ρ} (cv : [ Δ , Γ ] γ ∿ᵉ ρ ) → [ Δ , Ε ] π c ⊙ γ ∿ᵉ πᵉ c ρ
∿πᵉ Γ stop cv = ε
∿πᵉ .ε (step c () f) ε
∿πᵉ (Γ ∙[ x ∶ A ]⊣ f) (step {Δ} {y} {B} c occ f') cv =
  ∙ (∿≡ᵉ-cast Δ (≡*-sym (rstep ⊙-assoc (lstep (c∘₁ ∶⊙∶π) refl)))
    (∿πᵉ (Γ ∙[ x ∶ A ]⊣ f) c cv))
    (∿≡-cast B (≡*-sym (rstep :s⊙ (lstep (cs₁ :v₂) refl))) (∿-lookup _ occ cv))


mutual

  -- if p, P related by ∿ε  then t ⟨ ρ ⟩ ∿ ⟦ t ⟧t P
  lemma₈ : ∀ {A Γ Δ} M {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (cv : [ Δ , Γ ] γ ∿ᵉ ρ) → [ Δ , A ] M ⟨ γ ⟩ ∿ ⟦ M ⟧t ρ
  lemma₈ [ Γ ∋ x ↳ occ ] cv = ∿-lookup Γ occ cv
  lemma₈ {A ⇒ B} (∶λ x # f ⇨ t) cv =
   λ {Ε} c {N} {v} cvNv → ∿≡-cast B (≡*-sym (lstep (ca₁ :s⊙) (lstep :β refl))) (lemma₈ t
   (∙ (∿≡ᵉ-cast _ (≡*-sym (lstep ∶π∶ext refl)) (∿π _ c cv)) (∿≡-cast A (rstep :v₁ refl) cvNv)))
  lemma₈ {A} (M ⋆ N) cv =
    ∿≡-cast A (lstep (ca₁ :sid) (rstep :sapp refl)) (lemma₈ M cv P.refl (lemma₈ N cv))
  lemma₈ {A} (M ⟨ γ ⟩) cv = ∿≡-cast A (rstep :s⊙ refl) (lemma₈ M (lemma₈ˢ _ γ cv))

  -- lemma₈ but for substitutions, not terms
  -- i.e. if δ, ρ related by ∿ᵉ  then  (γ ⊙ δ)  ∿ᵉ  (⟦ γ ⟧s ρ)
  lemma₈ˢ : ∀ Γ {Δ} (γ : Δ ⇛ Γ) {Ε} {δ : Ε ⇛ Δ} {ρ : Ε ⊩ᵉ Δ} (cv : [ Ε , Δ ] δ ∿ᵉ ρ) → [ Ε , Γ ] γ ⊙ δ ∿ᵉ ⟦ γ ⟧s ρ
  lemma₈ˢ Γ (π c) cv = ∿πᵉ _ c cv
  lemma₈ˢ Γ (γ ⊙ δ) cv = ∿≡ᵉ-cast Γ (rstep ⊙-assoc refl) (lemma₈ˢ Γ γ (lemma₈ˢ _ δ cv))
  lemma₈ˢ (Γ ∙[ x ∶ A ]⊣ f) (γ [ .x ↦ M ]) cv = 
   ∙ (∿≡ᵉ-cast Γ (≡*-sym (rstep ⊙-assoc (lstep (c∘₁ ∶π∶ext) refl))) (lemma₈ˢ Γ γ cv))
      (∿≡-cast A (≡*-sym (lstep (cs₂ ∶ext∶⊙) (lstep :v₁ refl))) (lemma₈ M cv))


mutual 

  lemma₉ : ∀ {A Γ} M u (cv : [ Γ , A ] M ∿ u) → (Γ ⊢ A ∋ M ≅ reify Γ A u)
  -- base case = :sid and cv
  lemma₉ {♭} M u cv = ≡*-trans (rstep (:sid {_} {_} {P.refl}) refl) (cv _)      
  -- Goal. M ≅ λx. reify u (val x) 
 --  Given 
  -- cv : [ Δ , A ] N ∿ v → [ Δ , B ] (M ⟨ π c ⟩) ⋆ N ∿ u c v
  -- u : Γ ⊩ A ⇒ B = (Δ ≥ Γ)  (Δ ⊩ A) → (Δ ⊩ B) 
  -- reify Γ A u = 
  --    ∶λ (x≡fresh Γ) ⇨ (reify (Γ,x:A) B (u (Γ,x:A ≥ Γ) (val (Γ,x:A) A  (λ {Δ} (c : Δ ≥ (Γ,x:A)) → [ (Γ,x:A) ∋ x ↳ lemma₂ c here! ]))))
  -- 
  -- Now, 
  --  we have M ≅ ∶λ x # f ⇨ ((M ⟨ π c ⟩) ⋆ [ (Γ ∙[ x ∶ A ]⊣ f) ∋ x ↳ here! ]  
  --  also ∿-val, with Γ = Γ,x:A, the f constructed in reify for x, M = _ x ↳ here!  (i.e. the N we want for cv)
  --          gives us  _ x ↳ here! ∿ val Γ A f
  --  hence cv, with N=_ x ↳ here!, v = val Γ A f,  yields M ⟨π c⟩ ⋆  _ x ↳ here! ∿  u c (val x)     
  --       by IH we then know    M ⟨π c⟩ ⋆  _ x ↳ here! ≅  reify (u c (val x))
  --     by cong-λ, trans we are done.
  lemma₉ {A ⇒ B} {Γ} M u cv = 
        let 
           f : (Γ ∙[ fresh Γ ∶ A ]⊣ isfresh Γ) ⊢⇑ A
           f = λ {Δ} (c : Δ ≥ _) → [ _ ∋ fresh Γ ↳ lemma₂ c here! ]
           v : (Γ ∙[ fresh Γ ∶ A ]⊣ isfresh Γ) ⊩ A
           v = val (Γ ∙[ fresh Γ ∶ A ]⊣ isfresh Γ) A f
        in 
           lstep (:η {Γ}{A}{B}{fresh Γ}{isfresh Γ} M {lemma₅}) 
                 (≡*-cong cλ (lemma₉ ((M ⟨ π lemma₅ ⟩) ⋆ [ _ ∋ fresh Γ ↳ here! ]) 
                                                  (u lemma₅ v)
                                                  (cv lemma₅ {[ _ ∋ fresh Γ ↳ here! ]}
                                                                    {v}
                                                                    (∿-val {A} 
                                                                              {Γ ∙[ fresh Γ ∶ A ]⊣ isfresh Γ} 
                                                                               [ _ ∋ fresh Γ ↳ here! ]
                                                                               f
                                                                              (λ {Δ} c → lstep :v₂ refl)))))  

  -- so need some v s.t  [ (Γ, fresh Γ : A) , A ] [ _ ∋ fresh Γ ↳ here! ])  ∿ v
  -- using val need 
  --  ∀ {Δ}(c : Δ ≥ Γ, fresh Γ : A) → (_ ∋ fresh Γ ↳ here!) ⟨π c⟩ ≅  Δ ∋ fresh Γ ↳ lemma₂ c here!
  -- which is just :v₂


  ∿-val : ∀ {A Γ} M (f : Γ ⊢⇑ A)(h : ∀ {Δ} (c : Δ ≥ Γ) → Δ ⊢ A ∋ M ⟨ π c ⟩ ≅ f c) → [ Γ , A ] M ∿ val Γ A f
  ∿-val {♭} M f Mf≅ = Mf≅
  --      recall val Γ (A ⇒ B) f = 
  --                        λ {Δ} (c : Δ ≥ Γ) (a : Δ ⊩ A) →  
  --                              val Δ B (λ {Ε} (c' : Ε ≥ Δ) → f (P.trans c' c) ⋆ (reify Ε A ↑[ c' , A ]⟨ a ⟩))
  -- require M ⟨π c⟩ ⋆ N ∿ (val Γ (A ⇒ B) f) c v 
  --                               ∿ val Δ B (f' ≡ λ {Ε} (c' : Ε ≥ Δ) → f (P.trans c' c) ⋆ (reify Ε A ↑[ c' , A ]⟨ v ⟩))
  -- using IH of ∿-val with f'
  -- we need to provide h
  --  [ Δ' , B ] (((M ⟨ π c ⟩) ⋆ N) ⟨ π c'' ⟩) ≅ (f (P.trans c'' c) ⋆ reify Δ' A ↑[ c'' , A ]⟨ v ⟩)
  --  using N∿v, Mf≅ combine with ∿↑, :sapp, :s⊙, and recursive call to lemma₉ gives result.
  ∿-val {A ⇒ B} {Γ} M f Mf≅ = 
          λ {Δ} c {N} {v} N∿v → 
                ∿-val {B} {Δ} 
                          (M ⟨ π c ⟩ ⋆ N) 
                          (λ {Ε} (c' : Ε ≥ Δ) → f (P.trans c' c) ⋆ (reify Ε A ↑[ c' , A ]⟨ v ⟩)) 
                          (λ {Δ'} (c'' : Δ' ≥ Δ) → 
                               lstep :sapp (≡*-trans (≡*-cong ca₁ (lstep :s⊙ (lstep (cs₂ ∶⊙∶π) (Mf≅ (P.trans c'' c)) )))
                                                                (≡*-cong ca₂ (lemma₉ (N ⟨ π c'' ⟩) ↑[  c'' , A ]⟨ v ⟩ (∿↑ A c'' N∿v)))  ))

-- this is important.
π∿id↑ᵉ : ∀ {Δ Γ : Context} (c : Δ ≥ Γ) → [ Δ , Γ ] π c ∿ᵉ idᵉ↑ c
π∿id↑ᵉ {Δ} {ε} stop = ε
π∿id↑ᵉ {Δ} {Γ ∙[ x ∶ A ]⊣ f} c = 
    ∙ (∿π  Γ c (π∿id↑ᵉ lemma₅) )
       (∿↑ A c (∿-val {A} 
                               [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] 
                               (λ {Δ} inc → [ Δ ∋ x ↳ lemma₂ inc here! ])
                               ((λ {Δ} c → lstep :v₂ refl))))

-- recall 
--  lemma₈ : ∀ {A Γ Δ} M {γ : Δ ⇛ Γ} {ρ : Δ ⊩ᵉ Γ} (cv : [ Δ , Γ ] γ ∿ᵉ ρ) → [ Δ , A ] M ⟨ γ ⟩ ∿ ⟦ M ⟧t ρ
--  lemma₉ : ∀ {A Γ} M u (cv : [ Γ , A ] M ∿ u) → (Γ ⊢ A ∋ M ≅ reify Γ A u)
-- by π∿id↑ᵉ, lemma₈ , lemma₉ we get M⟨π c⟩≅nf(M) where c:Γ≥Γ,  since M≅M⟨π c⟩ by trans get result.
theorem₂ : ∀ {Γ A} (M : Γ ⊢ A) → Γ ⊢ A ∋ M ≅ nf M
theorem₂ {Γ} {A} M = 
     let 
          m₁ : [ Γ , A ] M ⟨ π P.refl ⟩ ∿ ⟦ M ⟧t (idᵉ↑ {Γ} P.refl)
          m₁ = (lemma₈ M (π∿id↑ᵉ P.refl))
          m₂ :  Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idᵉ↑ {Γ} P.refl) , ⟦ M ⟧t (idᵉ Γ) ]  
          m₂ = Eq-⟦⟧t-compat M (Uniᵉ↑ Γ P.refl (Uni-idᵉ {Γ})) (Uni-idᵉ {Γ}) (Eqᵉ↑-id Γ P.refl )
          m₃ :  Γ ⊢ A ∋ M ⟨ π P.refl ⟩ ≅ reify Γ A (⟦ M ⟧t (idᵉ↑ {Γ} P.refl))
          m₃ = lemma₉ (M ⟨ π P.refl ⟩) (⟦ M ⟧t _) m₁ 
          m₄ :  Γ ⊢ A ∋ M ⟨ π P.refl ⟩ ≅ reify Γ A (⟦ M ⟧t (idᵉ Γ))
          m₄ =  subst (λ M' → Γ ⊢ A ∋ M ⟨ π P.refl ⟩ ≅ M') (theorem₁ A m₂) m₃
     in rstep :sid m₄



-- now easy to prove Theorem 3. 
-- proof: know by corollary 1 that nf(M) ≡ nf(N) so ≅ by refl. 
--  by theorem₂ know M ≅ nf(M),  N ≅ nf(N), result follows trivially by sym, trans.
theorem₃ : ∀ {Γ A} M N (eq : Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idᵉ Γ) , ⟦ N ⟧t (idᵉ Γ) ]) → Γ ⊢ A ∋ M ≅ N
theorem₃ {Γ} {A} M N eq = 
  let 
    m1 :  Γ ⊢ A ∋ nf M ≅ nf N 
    m1 = subst (λ x → Γ ⊢ A ∋ nf M ≅ x) (corollary₁ {Γ} {A} {M} {N} eq) refl
    m2 :  Γ ⊢ A ∋ M ≅ nf M 
    m2 = theorem₂ M
    m3 :  Γ ⊢ A ∋ N ≅ nf N 
    m3 = theorem₂ N
  in ≡*-trans m2 (≡*-trans m1 (≡*-sym m3))



----- Completeness of substitution conversions. 
reifyˢ : ∀ Δ Γ (ρ : Δ ⊩ᵉ Γ) → (Δ ⇛ Γ)
reifyˢ Δ ε tt = π stop
reifyˢ Δ (Γ ∙[ x ∶ A ]⊣ f) (ρ , v) = (reifyˢ  Δ Γ ρ)[ x ↦ reify Δ A v ]

  -- Equal semantic values reify to elements in the same equivalence class of terms.  (simple induction on type)
theorem₁ˢ : ∀ {Δ} Γ {ρ₁ ρ₂} (eq : Eq⟨ Δ ⊩ᵉ Γ ⟩[ ρ₁ , ρ₂ ]) → reifyˢ Δ Γ ρ₁ ≡ reifyˢ Δ Γ ρ₂
theorem₁ˢ ε tt = refl
theorem₁ˢ (Γ ∙[ x ∶ A ]⊣ f) {ρ₁ , v₁} {ρ₂ , v₂} (eqρ , eqv) = 
       cong₂ (λ ρ M → ρ [ x ↦ M ]) (theorem₁ˢ Γ eqρ) (theorem₁ A eqv)


nfˢ : ∀ {Γ Δ} (M : Δ ⇛ Γ) → Δ ⇛ Γ
nfˢ {Γ} {Δ} γ = reifyˢ Δ Γ (⟦ γ ⟧s (idᵉ Δ))

-- corresponding corrolary.
corollary₁ˢ : ∀ {Δ Γ : Context} {γ δ : Δ ⇛ Γ} (eq : Eq⟨ Δ ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s (idᵉ Δ) , ⟦ δ ⟧s (idᵉ Δ) ]) → nfˢ γ ≡ nfˢ δ
corollary₁ˢ {Δ} {Γ} eq = theorem₁ˢ {Δ} Γ eq -- theorem₁ _ eq


-- completeness result follows from similar work as for proof trees. 
-- i.e. prove γ ≅ˢ nf γ   

-- Recall
--  lemma₈ˢ : ∀ Γ {Δ} (γ : Δ ⇛ Γ) {Ε} {δ : Ε ⇛ Δ} {ρ : Ε ⊩ᵉ Δ} (cv : [ Ε , Δ ] δ ∿ᵉ ρ) → [ Ε , Γ ] γ ⊙ δ ∿ᵉ ⟦ γ ⟧s ρ

-- will use :πε for ε and :ηε to step down a context in Γ ∙[ x : A ]⊣ f case. 
lemma₉ˢ : ∀ {Γ Δ} γ ρ (cvᵉ : [ Δ , Γ ] γ ∿ᵉ ρ) → (Δ ⊢ Γ ∋ γ ≅ˢ reifyˢ Δ Γ ρ)
lemma₉ˢ {ε} {Γ} γ ρ cvᵉ = lstep (:πε {Γ} {γ} {stop}) refl 
-- 
-- πγρ : [ .Δ , Γ ] (π lemma₅) ⊙ γ ∿ᵉ ρ
-- xv  : [ .Δ , A ] [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟨ γ ⟩ ∿ v 
-- recall :  lemma₉ : ∀ {A Γ} M u (cv : [ Γ , A ] M ∿ u) → (Γ ⊢ A ∋ M ≅ reify Γ A u)
-- using IHs reduces to 
-- (π lemma₅ ⊙ γ) [ x ↦ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟨ γ ⟩ ] ≅  (reifyˢ Δ Γ ρ) [ x ↦ reify Δ A v ]
-- solve easily by cong.
lemma₉ˢ {Γ ∙[ x ∶ A ]⊣ f} {Δ}  γ (ρ , v) (∙ πγρ xv) = 
   let 
     IH₁ : Δ ⊢ Γ ∋  (π lemma₅) ⊙ γ ≅ˢ reifyˢ Δ Γ ρ
     IH₁ = lemma₉ˢ {Γ} ((π lemma₅) ⊙ γ ) ρ πγρ
     IH₂ : Δ ⊢ A ∋ [ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟨ γ ⟩ ≅ reify Δ A v
     IH₂ = lemma₉ {A} ([ Γ ∙[ x ∶ A ]⊣ f ∋ x ↳ here! ] ⟨ γ ⟩) v xv
   in 
   lstep (:ηε x here! γ lemma₅) 
           (≡*-trans 
                 (≡*-cong c≔₁ IH₁ )
                 (≡*-cong c≔₂ IH₂) )
     


theorem₂ˢ : ∀ {Δ Γ} (γ : Δ ⇛ Γ) → Δ ⊢ Γ ∋ γ ≅ˢ nfˢ γ
theorem₂ˢ {Δ} {Γ} γ = 
    let 
      m₁ : [ Δ , Γ ] γ ⊙ (π P.refl) ∿ᵉ ⟦ γ ⟧s (idᵉ↑ {Δ} P.refl)
      m₁ = lemma₈ˢ Γ γ (π∿id↑ᵉ P.refl)
      m₂ :  Δ ⊢ Γ ∋ γ ⊙ (π P.refl ) ≅ˢ reifyˢ Δ Γ (⟦ γ ⟧s (idᵉ↑ {Δ} P.refl))
      m₂  = lemma₉ˢ (γ ⊙ (π P.refl)) (⟦ γ ⟧s _) m₁ 
      m₃ :  Eq⟨ Δ ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s (idᵉ↑ {Δ} P.refl) , ⟦ γ ⟧s (idᵉ Δ) ]  
      m₃ = Eq-⟦⟧s-compat γ (Uniᵉ↑ Δ P.refl (Uni-idᵉ {Δ})) (Uni-idᵉ {Δ}) (Eqᵉ↑-id Δ P.refl )
      m₄ :  Δ ⊢ Γ ∋  (γ ⊙ (π P.refl)) ≅ˢ reifyˢ Δ Γ (⟦ γ ⟧s (idᵉ Δ))
      m₄ =  subst (λ γ' → Δ ⊢ Γ ∋ γ ⊙ (π P.refl) ≅ˢ γ') (theorem₁ˢ Γ m₃) m₂
    in 
    rstep :πid m₄ 


theorem₃ˢ : ∀ {Δ Γ} (γ δ : Δ ⇛ Γ) (eq : Eq⟨ Δ ⊩ᵉ Γ ⟩[ ⟦ γ ⟧s (idᵉ Δ) , ⟦ δ ⟧s (idᵉ Δ) ]) → Δ ⊢ Γ ∋ γ ≅ˢ δ
theorem₃ˢ {Δ} {Γ} γ δ eq = 
  let 
    m1 :  Δ ⊢ Γ ∋ nfˢ γ ≅ˢ nfˢ δ
    m1 = subst (λ γ' → Δ ⊢ Γ ∋ nfˢ γ ≅ˢ γ') (corollary₁ˢ {Δ} {Γ} {γ} {δ} eq) refl
    m2 :  Δ ⊢ Γ ∋ γ ≅ˢ nfˢ γ 
    m2 = theorem₂ˢ γ
    m3 :  Δ ⊢ Γ ∋ δ ≅ˢ nfˢ δ 
    m3 = theorem₂ˢ δ
  in ≡*-trans m2 (≡*-trans m1 (≡*-sym m3))



-- Theorem5 ∈ (nf(M)≡nf(N)) → M ≅ N   (Decision algorithm is correct)
-- by Theorem2 we have M ≅ nf(M) and N ≅ nf(N) and, by hypothesis, nf(M)≡nf(N) and ≅-refl,
-- we get by transitivity of ≅, that M ≅ N.
theorem₅ : ∀ {Γ A}(M N : Γ ⊢ A)(idnf : nf M ≡ nf N) → Γ ⊢ A ∋ M ≅ N
theorem₅ {Γ} {A} M N idnf = ≡*-trans (theorem₂ M) 
                                                           (≡*-trans (subst (λ x → Γ ⊢ A ∋ nf M ≅ x) idnf refl) 
                                                                          (≡*-sym (theorem₂ N)))

-- Theorem6 ∈ (M ≅ N) → nf(M) ≡ nf(N)    (Decision algorithm is complete)
-- since by Theorem4 and the hypothesis, M≅N we get Eq([M]id,[N]id) and by corollary1 
-- we get nf M ≡ nf N.
-- recall corollary₁ : ∀ {Γ A} {M N : Γ ⊢ A} (eq : Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idᵉ Γ) , ⟦ N ⟧t (idᵉ Γ) ]) → nf M ≡ nf N
theorem₆ : ∀ {Γ A} (M N : Γ ⊢ A)(cv : Γ ⊢ A ∋ M ≅ N) → nf M ≡ nf N
theorem₆ {Γ} {A} M N cv = 
         let  
           nfeq : Eq⟨ Γ ⊩ A ⟩[ ⟦ M ⟧t (idᵉ Γ) , ⟦ N ⟧t (idᵉ Γ) ]
           nfeq = theorem₄ M N cv (idᵉ Γ) (Uni-idᵉ {Γ})
         in 
         corollary₁ {Γ} {A} {M} {N} nfeq


-- similar theorems (theorem₅ˢ theorem₆ˢ can easily be given)


--- Normal forms

mutual 
  data enf : ∀ {Γ A}(M : Γ ⊢ A) → Set where
    enf1 : ∀ {Γ x A B f}(M : Γ ∙[ x ∶ A ]⊣ f ⊢ B)(Me : enf M) → enf (∶λ x # f ⇨ M)
    enf2 : ∀ {Γ}(M : Γ ⊢ ♭)(Ma : anf M) → enf M

  data anf : ∀ {Γ A}(M : Γ ⊢ A) → Set where
    anf1 : ∀ {Γ x A}{occ : [ x ∶ A ]∈ Γ} → anf [ Γ ∋ x ↳ occ ]
    anf2 : ∀ {Γ A B} (M : Γ ⊢ A ⇒ B) (N : Γ ⊢ A)(Ma : anf M)(Ne : enf N) → anf (M ⋆ N)

-- Goal: prove enf(nf M)  
--  define kripke logical predicate KN , such that KN⟦M⟧ and if KN(u), then enf(reify u).
--  as before we define by induction on the type.
NV : ∀ {Γ A} (v : Γ ⊩ A) → Set
NV {Γ} {♭} v = ∀ {Δ} (c : Δ ≥ Γ) → anf (v c)
NV {Γ} {A ⇒ B} v = ∀ {Δ : Context} (c : Δ ≥ Γ) (u : Δ ⊩ A) (nu : NV {Δ} {A} u) → NV {Δ} {B} (v c u)


-- similar property of substitutions.
-- option 1
NVᵉ : ∀ {Δ} {Γ} (ρ : Δ ⊩ᵉ Γ) → Set
NVᵉ {Δ} {ε} tt = ⊤
NVᵉ {Δ} {Γ ∙[ x ∶ A ]⊣ f} (ρ , v) = NVᵉ {Δ} {Γ} ρ × NV {Δ} {A} v

-- option 2 (data)
-- data NVε : ∀ {Δ Γ} (ρ : Δ ⊩ᵉ Γ) → Set where
--   εN : ∀ {Δ} → NVε {Δ} {ε} tt
--   ∙N : ∀ {Δ Γ x A f} {ρ : Δ ⊩ᵉ Γ} (nρ : NVε {Δ} {Γ} ρ) {v : Δ ⊩ A} (nv : NV {Δ} {A} v) → NVε {Δ} {Γ ∙[ x ∶ A ]⊣ f} (ρ , v)


-- lemmas from 77

-- (v : Δ ⊩ A) N(v) (c : Γ≥Δ) → N(↑c(v))
NV↑ : ∀ {Δ Γ A} (v : Γ ⊩ A) (nv : NV {Γ} {A}  v) (c : Δ ≥ Γ)  →  NV {Δ} {A} ↑[ c , A ]⟨ v ⟩
NV↑ = {!!} 

--   lookup : ∀ {w} Γ (ρ : w ⊩ᵉ Γ) {x A} (occ : [ x ∶ A ]∈ Γ) → w ⊩ A
NV-lookup : ∀ {Δ Γ A x} (ρ : Δ ⊩ᵉ Γ) (nρ : NVᵉ {Δ} {Γ} ρ) (occ : [ x ∶ A ]∈ Γ) → NV {Δ} {A} (lookup Γ ρ occ)
NV-lookup = {!!}

-- (ρ : Γ₀ ⊩ᵉ Δ) N(ρ) (c : Γ₁ ≥ Γ₀) → N(↑c(ρ)) 
NVᵉ↑ : ∀ {Θ Δ Γ} (ρ : Δ ⊩ᵉ Γ) (nρ : NVᵉ {Δ} {Γ} ρ) (c : Θ ≥ Δ) → NVᵉ {Θ} {Γ} ↑ᵉ[ c , Γ ]⟨ ρ ⟩ 
NVᵉ↑ = {!!} 

-- (ρ : Γ ⊩ᵉ Δ₁) N(ρ) (c : Δ₁ ≥ Δ₀) N(↓c(ρ))
NVᵉπ : ∀ {Δ Γ₂ Γ₁} (ρ : Δ ⊩ᵉ Γ₂) (nρ : NVᵉ {Δ} {Γ₂} ρ) (c : Γ₂ ≥ Γ₁) → NVᵉ {Δ} {Γ₁} (πᵉ c ρ)
NVᵉπ = {!!} 

mutual 
  lemma₁₀ :  ∀ {Δ Γ A} (M : Γ ⊢ A) (ρ : Δ ⊩ᵉ Γ) (nρ : NVᵉ {Δ}{Γ} ρ) → NV {Δ} {A} (⟦ M ⟧t ρ)
  lemma₁₀ = {!!} 

  lem₁₀ˢ : ∀ {Θ Δ Γ} (γ : Δ ⇛ Γ) (ρ : Θ ⊩ᵉ Δ) (nρ : NVᵉ {Θ} {Δ} ρ) → NVᵉ {Θ} {Γ} (⟦ γ ⟧s ρ)
  lem₁₀ˢ = {!!}

mutual 
  -- proof by induction on type
  lemma₁₁ : ∀ {Γ A} (v : Γ ⊩ A) (vn : NV {Γ}{A} v) → enf (reify Γ A v)
  lemma₁₁ = {!!}

  lemma₁₁ˢ :  ∀ {Γ A} (f : Γ ⊢⇑ A)(h : ∀ {Δ} (c : Δ ≥ Γ) → anf (f c)) → NV {Γ} {A} (val Γ A f)
  lemma₁₁ˢ = {!!}

-- Now easy to show NV id 
NVᵉid : ∀ {Γ : Context } → NVᵉ {Γ} {Γ} (idᵉ Γ)
NVᵉid = {!!}


-- by simple application of lemma 10 and lemma 11
theorem₇ : ∀ {Γ A} (M : Γ ⊢ A) → enf (nf M)
theorem₇ = {!!} 


-- Todo-Exercise: paper says we can use these results to show that 
-- (λ x:A.M) ≅ (λ y:A.N) ⇒ M ⟨x ↦ z⟩ ≅ N⟨y ↦ z⟩ for z fresh 
-- i.e.
-- Γ ⊢ A ⇒ B ∋ (∶λ x # f . M) ≅ (∶λ y # f . N)
--         → M ⟨ π (P.refl Γ) [ x ↦ z ] ⟩ ≅ N ⟨ π (P.refl Γ) [ y ↦ z ] ⟩ 


