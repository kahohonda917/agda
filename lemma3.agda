module lemma3 where

open import DSt2
open import CPSt2

open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality

subst-cont  : {var : cpstyp → Set} {τ₁ τ₂ : typ} {μα : trail} {τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubstVal (λ x → v₁ x) v v₁′ →
  cpsSubst (λ x → k₁ x (v₁ x) (t′)) v (k₂ v₁′ t′)

subst-cont′ : {var : cpstyp → Set} {τ₁ τ₂ : typ} {μα : trail} {τ₃ : cpstyp} →
              (k₁ : var τ₃ → cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) →
              (v : cpsvalue[ var ] τ₃) →
              (k₂ : cpsvalue[ var ] (cpsT τ₁) →
               cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT τ₂)) → Set

subst-cont′ {var} {τ₁} {τ₂} {μα} {τ₃} k₁ v k₂ =
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  {t′ : cpsvalue[ var ] (cpsM μα)} →
  cpsSubst (λ x → k₁ x v₁′ (t′)) v (k₂ v₁′ t′)

mutual
  SubstV≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t

  SubstV≠ {var} {t = CPSVar x} = sVar≠
  SubstV≠ {var} {t = CPSNum n} = sNum
  SubstV≠ {var} {t = CPSFun e} = sFun λ x → Subst≠
  SubstV≠ {var} {t = CPSId} = sId
  SubstV≠ {t = CPSAppend x t t₁} = sApd SubstV≠ SubstV≠
  SubstV≠ {t = CPSCons x t t₁} = sCon SubstV≠ SubstV≠

  Subst≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
           {t : cpsterm[ var ] τ₁} →
           {v : cpsvalue[ var ] τ₂} →
           cpsSubst (λ y → t) v t

  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp t t₁} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet t x} = sLet (λ y → Subst≠) (λ y₂ → Subst≠)
  Subst≠ {t = CPSPlus t t₁} = sPlu Subst≠ Subst≠
  Subst≠ {t = CPSIdk x x₁ t} = sIdk SubstV≠ SubstV≠

mutual
  SubstV-id : {var : typ → Set} {τ₁ τ₂ : typ} →
              {v₁ : value[ var ] τ₁} →
              {v : value[ var ] τ₂} →
              SubstVal (λ _ → v₁) v v₁
  SubstV-id {var} {τ₁} {τ₂} {Var x} {v} = sVar≠
  SubstV-id {var} {.Nat} {τ₂} {Num n} {v} = sNum
  SubstV-id {var} {.(_ ⇒ _ ⟨ _ ⟩ _ ⟨ _ ⟩ _)} {τ₂} {Fun e₁} {v} =
    sFun λ x → Subst-id

  Subst-id : {var : typ → Set} {τ₁ τ₂ α β : typ} {μα μβ : trail} →
             {μs : trails[ μβ ] μα}
             {t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ] τ₂} →
             Subst (λ _ → t) v t
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {t = Val x} {v} =
    sVal SubstV-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = App t t₁} {v} =
    sApp Subst-id Subst-id
  Subst-id {var} {.Nat} {τ₂} {α} {β} {μα} {μβ} {t = Plus t t₁} {v} =
    sPlu Subst-id Subst-id
  Subst-id {var} {τ₁} {τ₂} {α} {β} {μα} {μβ} {t = Control x x₁ x₂ e} {v} =
    sCon (λ k → Subst-id)
  Subst-id {var} {τ₁} {τ₂} {α} {.α} {μα} {.μα} {t = Prompt x t} {v} =
    sPro Subst-id

-- schematic
schematicV : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} →
             (k : cpsvalue[ var ] (cpsT τ₁) →
             cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             Set
schematicV {var} {τ₁} {μα = μα} k =
  (v : value[ var ∘ cpsT ] τ₁) →
  (t : cpsvalue[ var ] cpsM μα) →
  cpsSubst (λ x → k (CPSVar x) t) (cpsV v) (k (cpsV v) t)

schematic : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} →
            (k : cpsvalue[ var ] (cpsT τ₁) →
                 cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
            Set
schematic  {var} {τ₁} {μα = μα} k =
  (v : cpsvalue[ var ] (cpsT τ₁)) →
  (t : cpsvalue[ var ] cpsM μα) →
  cpsSubst (λ x → k (CPSVar x) t) v (k v t)

schematicV′ : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} →
              (k : cpsvalue[ var ] (cpsT τ₁) →
                   cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
schematicV′ {var} {τ₁} {μα = μα} k =
  (t : cpsvalue[ var ] (cpsM μα)) →
  (v₂ : cpsvalue[ var ] cpsT τ₁) →
  cpsSubst (λ x → k v₂ (CPSVar x)) t (k v₂ t)

schematicK : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} {τ : cpstyp} →
             (k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
                  cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
             Set
schematicK  {var} {τ₁} {μα = μα} {τ = τ} k =
  {v : cpsvalue[ var ] τ} →
  (x : cpsvalue[ var ] (cpsT τ₁)) →
  (t : cpsvalue[ var ] cpsM μα) →
  cpsSubst (λ x₁ → k (CPSVar x₁) x t) v (k v x t)

{-
schematicK′ : {var : cpstyp → Set} {τ₁ α : typ} {μα : trail} {τ : cpstyp} →
              (k : var τ → cpsvalue[ var ] (cpsT τ₁) →
                   cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
              Set
schematicK′  {var} {τ₁} {α} {μα = μα} {τ = τ} k =
  {v : var τ} →
  (x : cpsvalue[ var ] (cpsT τ₁)) →
  (t : cpsvalue[ var ] cpsM μα) →
  {k₂ : cpsvalue[ var ] (cpsT τ₁) →
        cpsvalue[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)} →
  cpsSubst (λ x₁ → k x₁ x t) (CPSVar v) (k₂ x t)
-}

mutual
  eSubstV : {var : cpstyp → Set} {τ₁ τ : typ} →
            {v₁ : var (cpsT τ) → value[ var ∘ cpsT ] τ₁} →
            {v₁′ : value[ var ∘ cpsT ] τ₁} →
            {v : value[ var ∘ cpsT ] τ} →
            SubstVal v₁ v v₁′ →
            cpsSubstVal (λ y → cpsV {var = var} (v₁ y)) (cpsV v) (cpsV v₁′)
  eSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  eSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  eSubstV SubstVal.sNum = cpsSubstVal.sNum
  eSubstV (sFun sub) =
    sFun (λ x → sVal (sFun (λ x₁ → sVal (sFun (λ x₂ →
      eSubst (sub x) (λ x₃ → sApp (sApp Subst≠ (sVal x₃)) Subst≠))))))

  eSubst : {var : cpstyp → Set} {τ₁ α β τ : typ} {μα μβ : trail}
           {μs : trails[ μβ ] μα} →
           {e₁ : var (cpsT τ) → term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
           {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
           {v : value[ var ∘ cpsT ] τ} →
           {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                cpsterm[ var ] (cpsT α)} →
           {t :  cpsvalue[ var ] cpsM μβ} →
           Subst e₁ v e₂ →
           subst-cont (λ x → k) (cpsV v) k →
           cpsSubst (λ x → cpsTerm (e₁ x) k t) (cpsV v)
           (cpsTerm e₂ k t)
  eSubst (sVal x) eq = eq (eSubstV x)
  eSubst (sApp x x₂) eq =
    ekSubst x (λ x₁ → ekSubst x₂ (λ x₃ →
      sApp (sApp (sApp (sVal x₁) (sVal x₃)) Subst≠) Subst≠))
  eSubst (sPlu x x₂) eq =
    ekSubst x (λ x₁ →
      ekSubst x₂ (λ x₃ →
        sLet (λ x₄ → Subst≠) (λ x₄ → sPlu (sVal x₁) (sVal x₃))))
  eSubst (sCon x) eq =
    sLet (λ x₂ → eSubst (x x₂) (λ x₆ → sIdk x₆ SubstV≠)) (λ x₂ → Subst≠)
  eSubst (sPro x) eq =
    sLet (λ x₂ → Subst≠) (λ x₄ → eSubst x (λ x₅ → sIdk x₅ SubstV≠))

  kSubst′′ : {var : cpstyp → Set} {τ₁ α β : typ}
             {μα μβ : trail} {μs : trails[ μβ ] μα} {τ : cpstyp} →
             (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
             {v : cpsvalue[ var ] τ} →
             {k₁ : var τ →
                   cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                   cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                   cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsvalue[ var ] (cpsM μβ)} →
             (sub-k : subst-cont k₁ v k₂) →
             cpsSubst (λ x → cpsTerm e (k₁ x) t₁) v (cpsTerm e k₂ t₁)
  kSubst′′ (Val v) sub-k = sub-k SubstV≠
  kSubst′′ (App e₁ e₂) sub-k =
    kSubst′′ e₁ (λ sub-v₁ →
      kSubst′′ e₂ (λ sub-v₂ →
        sApp (sApp (sApp (sVal sub-v₁) (sVal sub-v₂))
                   (sVal (sFun (λ v → sVal (sFun (λ t → sub-k SubstV≠))))))
             Subst≠))
  kSubst′′ (Plus e₁ e₂) sub-k =
    kSubst′′ e₁ (λ sub-v₁ →
      kSubst′′ e₂ (λ sub-v₂ →
        sLet (λ x → sub-k SubstV≠)
             (λ n → sPlu (sVal sub-v₁) (sVal sub-v₂))))
  kSubst′′ (Control id c₁ c₂ e) sub-k =
    sLet (λ x → Subst≠)
         (λ x → sVal (sFun (λ v → sVal (sFun (λ k → sVal (sFun (λ t →
                  sLet (λ t' → sub-k SubstV≠)
                       (λ t' → Subst≠))))))))
  kSubst′′ (Prompt id e) sub-k =
    sLet (λ x → sub-k SubstV≠)
         (λ x → Subst≠)

  kSubst : {var : cpstyp → Set} {τ₁ α β : typ}
           {μα μβ : trail} {μs : trails[ μβ ] μα} {τ : cpstyp} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] τ} →
           {k : cpsvalue[ var ] τ → cpsvalue[ var ] (cpsT τ₁) →
                 cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
           {t : cpsvalue[ var ] (cpsM μβ)} →
           (sch : schematicK k) →
           cpsSubst (λ x → cpsTerm e (k (CPSVar x)) t) v
                    (cpsTerm e (k v) t)

  kSubst (Val v) {t = t} sch = sch (cpsV v) t
  kSubst (App e₁ e₂) sch =
    kSubst e₁ (λ v₁ t₁ →
      kSubst e₂ (λ v₂ t₂ →
        sApp (sApp Subst≠
                   (sVal (sFun λ x₁ → sVal (sFun (λ x₂ →
                     sch (CPSVar x₁) (CPSVar x₂))))))
             Subst≠))
  kSubst (Plus e₁ e₂) sch =
    kSubst e₁ (λ v₁ t₁ →
      kSubst e₂ (λ v₂ t₂ →
        sLet (λ n → sch (CPSVar n) t₂)
             (λ n → Subst≠)))
  kSubst (Control id c₁ c₂ e) sch =
    sLet (λ x → Subst≠)
         (λ x → sVal (sFun (λ v → sVal (sFun (λ k → sVal (sFun (λ t →
                   sLet (λ t' → sch (CPSVar v) (CPSVar t'))
                        (λ t' → Subst≠))))))))
  kSubst (Prompt id e) {t = t} sch =
    sLet (λ x → sch (CPSVar x) t)
         (λ x → Subst≠)

  tSubst : {var : cpstyp → Set} {τ₁ α β : typ}
           {μα μβ : trail} {μs : trails[ μβ ] μα} →
           (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
           {v : cpsvalue[ var ] (cpsM μβ)} →
           {k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                cpsterm[ var ] (cpsT α)} →
           (sch : schematicV′ k) →
           cpsSubst (λ x → cpsTerm e k (CPSVar x)) v (cpsTerm e k v)

  tSubst (Val v₁) {v = v} sch = sch v (cpsV v₁)
  tSubst (App e₁ e₂) sch =
    tSubst e₁ (λ t₁ v₁ →
      tSubst e₂ (λ t₂ v₂ →
        sApp Subst≠ (sVal sVar=)))
  tSubst (Plus e₁ e₂) sch =
    tSubst e₁ (λ t₁ v₁ →
      tSubst e₂ (λ t₂ v₂ →
        sLet (λ n → sch t₂ (CPSVar n))
             (λ n → Subst≠)))
  tSubst (Control id c₁ c₂ e) sch =
    sLet (λ x → Subst≠)
         (λ x → sVal (sFun (λ v → sVal (sFun (λ k → sVal (sFun (λ t →
                  sLet (λ t' → Subst≠)
                       (λ t' → sVal (sApd sVar= SubstV≠)))))))))
  tSubst (Prompt id e) {v = v} sch =
    sLet (λ x → sch v (CPSVar x))
         (λ x → Subst≠)

  ekSubst  : {var : cpstyp → Set} {τ τ₁ α β : typ}
             {μα μβ : trail} {μs : trails[ μβ ] μα} →
             {e₁ : (var ∘ cpsT) τ →
                   term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {e₂ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             {v : value[ var ∘ cpsT ] τ} →
             {k₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) →
                   cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {k₂ : cpsvalue[ var ] (cpsT τ₁) →
                   cpsvalue[ var ] (cpsMs μs) → cpsterm[ var ] (cpsT α)} →
             {t₁ : cpsvalue[ var ] (cpsM μβ)} →
             Subst e₁ v e₂ →
             (eq : subst-cont k₁ (cpsV v) k₂) →
             cpsSubst (λ y → cpsTerm (e₁ y) (k₁ y) t₁) (cpsV v)
                     (cpsTerm e₂ k₂ t₁)

  ekSubst (sVal v) eq = eq (eSubstV v)
  ekSubst (sApp sub₁ sub₂) eq =
    ekSubst sub₁ (λ m →
      ekSubst sub₂ (λ n →
        sApp (sApp (sApp (sVal m) (sVal n))
                   (sVal (sFun (λ x → sVal (sFun (λ x₁ → eq SubstV≠))))))
             Subst≠))
  ekSubst (sPlu sub₁ sub₂) eq =
    ekSubst sub₁ (λ m →
      ekSubst sub₂ (λ n →
        sLet (λ x → eq SubstV≠)
             (λ x → sPlu (sVal m) (sVal n))))
  ekSubst (sCon e) eq =
    sLet (λ x → ekSubst (e x) (λ v → sIdk v SubstV≠))
         (λ x → sVal (sFun (λ v → sVal (sFun λ k → sVal (sFun (λ t →
                  sLet (λ t' → eq SubstV≠) (λ t' → Subst≠)))))))
  ekSubst (sPro e) eq =
    sLet (λ v → eq SubstV≠)
         (λ v → ekSubst e (λ t → sIdk t SubstV≠))

correctCont : {var : cpstyp → Set} {τ₁ α β : typ}
              {μα μβ : trail} {μs : trails[ μβ ] μα} →
              (e : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) →
              (k₁ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                    cpsterm[ var ] (cpsT α)) →
              {k₂ : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                    cpsterm[ var ] (cpsT α)} →
              {t : cpsvalue[ var ] (cpsM μβ)} →
              (sch : schematic k₁) →
              (eq : (v : value[ var ∘ cpsT ] τ₁) →
                    (t : cpsvalue[ var ] (cpsMs μs)) →
                    cpsreduce (k₁ (cpsV v) t) (k₂ (cpsV v) t)) →
              cpsreduce (cpsTerm e k₁ t) (cpsTerm e k₂ t)

correctCont (Val v) k₁ {t = t} sch eq = eq v t
correctCont (App e₁ e₂) k₁ {k₂} {t} sch eq = begin
    cpsTerm e₁
    (λ z z₁ →
       cpsTerm e₂
       (λ z₂ z₃ →
          CPSApp
          (CPSApp (CPSApp (CPSVal z) (CPSVal z₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ v₁ → k₁ (cpsV (Var v)) (CPSVar v₁)))))))
          (CPSVal z₃))
       z₁)
    t
  ⟶⟨ correctCont e₁ _
        (λ v₁ t₁ → kSubst e₂
          (λ v₂ t₂ → sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
        (λ v₁ t₁ →
        correctCont e₂ _
          (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
          (λ v₂ t₂ →
          rApp₁ (rApp₂ (rFun (λ x₁ → rFun (λ x₂ →
            eq (Var x₁) (CPSVar x₂))))))) ⟩
      cpsTerm e₁
      (λ v₁ →
         cpsTerm e₂
         (λ v₂ t₂ →
            CPSApp
            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))
            (CPSVal t₂)))
      t
  ∎
correctCont (Plus e₁ e₂) k₁ {k₂} {t} sch eq = begin
    cpsTerm e₁
     (λ v₁ →
        cpsTerm e₂
        (λ v₂ t₂ →
           CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₁ (CPSVar v) t₂)))
     t
  ⟶⟨ correctCont e₁ _
        (λ v₁ t₁ → kSubst e₂
          (λ v₂ t₂ → sLet (λ n → Subst≠)
                          (λ n → sPlu (sVal sVar=) Subst≠)))
        (λ v₁ t₁ →
        correctCont e₂ _
          (λ v₂ t₂ → sLet (λ n → Subst≠)
                          (λ n → sPlu Subst≠ (sVal sVar=)))
          (λ v₂ t₂ →
          rLet₂ (λ n → eq (Var n) t₂))) ⟩
    cpsTerm e₁
     (λ v₁ →
        cpsTerm e₂
        (λ v₂ t₂ →
           CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂)) (λ v → k₂ (CPSVar v) t₂)))
     t
  ∎
correctCont (Control id c₁ c₂ e) k₁ {k₂} {t} sch eq = begin
      (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₂ t (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ k → rFun (λ t' →
               rLet₂ (λ t'' → eq (Var x) (CPSVar t'')))))) ⟩
      (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal (CPSAppend c₂ t (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → k₂ (CPSVar v) (CPSVar t'')))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
  ∎
correctCont (Prompt id e) k₁ {k₂} {t} sch eq =
  rLet₂ (λ x → eq (Var x) t)

mutual
  pSubstV≠ : {var : typ → Set} {τ₁ τ₂ : typ} →
             {t : value[ var ] τ₁ } →
             {v : value[ var ] τ₂ } →
             SubstVal (λ y → t) v t

  pSubstV≠ {t = Var x} = sVar≠
  pSubstV≠ {t = Num n} = sNum
  pSubstV≠ {t = Fun e₁} = sFun (λ x → pSubst≠)

  pSubst≠ : {var : typ → Set} {τ₁ τ₂ α β : typ}
            {μα μβ : trail} {μs : trails[ μβ ] μα} →
            {t : term[ var ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
            {v : value[ var ] τ₂ } →
            Subst (λ y → t) v t

  pSubst≠ {t = Val x} = sVal pSubstV≠
  pSubst≠ {t = App t t₁} = sApp pSubst≠ pSubst≠
  pSubst≠ {t = Plus t t₁} = sPlu pSubst≠ pSubst≠
  pSubst≠ {t = Control x x₁ x₂ e} = sCon (λ k → pSubst≠)
  pSubst≠ {t = Prompt x t} = sPro pSubst≠

subst-context : {var : typ → Set} {τ α τ₁ τ₂ α' : typ}
                {μα μ₁ μ₂ : trail} {μt : trails[ μ₂ ] μ₁} →
                (con : pcontext[ var , τ ⟨ []{μα} ⟩ α ⟨ μα ⟩ α ]
                                 τ₁ ⟨ μt ⟩ τ₂ ⟨ μ₂ ⟩ α' ) →
                (v : value[ var ] τ) →
                Subst (λ x → pcontext-plug con (Val (Var x))) v
                      (pcontext-plug con (Val v))

subst-context Hole v = sVal sVar=
subst-context (Frame (App₁ e₂) con) v = sApp (subst-context con v) pSubst≠
subst-context (Frame (App₂ v₁) con) v = sApp pSubst≠ (subst-context con v)
subst-context (Frame (Plus₁ e₂) con) v = sPlu (subst-context con v) pSubst≠
subst-context (Frame (Plus₂ v₁) con) v = sPlu pSubst≠ (subst-context con v)

-- control lemma
control-lemma : {var : cpstyp → Set} {τ τ₁ τ₂' τ₅ α β t₁ t₂ : typ}
              {μ₀ μ₂ μ₁ μα μβ μα' μγ : trail}
              {μ[β]γ : trails[ μβ ] μγ} →
              {μ[α]γ : trails[ μα ] μγ} →
              {μ[β]α : trails[ μβ ] μα} →
              (p₁ : pcontext[ var ∘ cpsT , τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β ]
                            τ₁ ⟨ μ[β]γ ⟩ τ₅ ⟨ μβ ⟩ β ) →
              (p₂ : pcontext[ var ∘ cpsT , τ ⟨ []{μα'} ⟩ τ₂' ⟨ μα' ⟩ τ₂' ]
                            τ₁ ⟨ μ[α]γ ⟩ τ₅ ⟨ μα ⟩ α ) →
              (c₁ : compatible (t₁ ⇒ t₂ , μ₁) μ₂ μ₀) →
              (c₂ : compatible μβ μ₀ μα) →
              same-pcontext p₁ p₂ →
              (e : term[ var ∘ cpsT ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β) →
              (k₁ : cpsvalue[ var ] cpsT τ₁ → cpsvalue[ var ] cpsM μγ →
                    cpsterm[ var ] cpsT τ₅) →
              (tr : cpsvalue[ var ] cpsM μβ) →
              (sch : schematic k₁) →
              (sch' : schematicV′ k₁) →
              cpsreduce
               (cpsTerm (pcontext-plug p₁ e) k₁ tr)
               (cpsTerm {μs = μ[β]γ}
                 (App {μ[γ]β = μ[β]α}
                      (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x)))))
                      e)
                 k₁ tr)

-- control-lemma = {!!}

--  control lemma starts
control-lemma {μ[β]α = μ[β]α} .Hole .Hole c₁ c₂ Hole e k₁ tr sch sch' =
  begin
    (cpsTerm (pcontext-plug Hole e) k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm e k₁ tr)
  ⟵⟨ correctCont e _
        (λ v t → sApp (sVal (sFun (λ x → sch v (CPSVar x))))
                      Subst≠)
        (λ v t → rBeta (sch' t (cpsV v))) ⟩
    cpsTerm e
       (λ v t →
             CPSApp (CPSVal (CPSFun (λ t'' →
                              k₁ v (CPSVar t''))))
                    (CPSVal t))
       tr
  ⟵⟨ correctCont e _
        (λ v t → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t → rApp₁ (rBeta (sVal (sFun (λ x →
                                 sch (cpsV v) (CPSVar x)))))) ⟩
    cpsTerm e
       (λ v t →
             CPSApp (CPSApp (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t'' →
                              k₁ (CPSVar v) (CPSVar t''))))))
                            (CPSVal v))
                    (CPSVal t))
       tr
  ⟵⟨ correctCont e _
        (λ v t → sApp (sVal (sFun (λ x →
                         sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))
                       Subst≠)
        (λ v t → rBeta (sApp Subst≠ (sVal sVar=))) ⟩
    cpsTerm e
       (λ v t →
          CPSApp
           (CPSVal (CPSFun (λ t' →
             CPSApp (CPSApp (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t'' →
                              k₁ (CPSVar v) (CPSVar t''))))))
                            (CPSVal v))
                    (CPSVal (CPSVar t')))))
          (CPSVal t))
       tr
  ⟵⟨ correctCont e _
        (λ v t → sApp (sApp (sVal (sFun (λ x → sVal (sFun (λ x₁ →
                               sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))
                             Subst≠)
                       Subst≠)
        (λ v t → rApp₁ (rBeta (sVal (sFun (λ x →
                                 sApp (sApp (sVal sVar=) Subst≠) Subst≠))))) ⟩
    cpsTerm e
       (λ v t →
          CPSApp
          (CPSApp
           (CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
             CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v))
                    (CPSVal (CPSVar t')))))))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t))
       tr
  ⟵⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k' → sVal (sFun (λ t' →
                   sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))))) ⟩
    (cpsTerm e
     (λ v t →
        CPSApp
        (CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ x →
               CPSVal
               (CPSFun
                (λ k' →
                   CPSVal
                   (CPSFun
                    (λ t' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar x)))
                       (CPSVal (CPSVar t')))))))))
          (CPSVal v))
         (CPSVal
          (CPSFun
           (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
        (CPSVal t))
     tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]α}
     (App (Val (Fun (λ x → Val (Var x)))) e) k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]α}
     (App (Val (Fun (λ x → pcontext-plug Hole (Val (Var x))))) e) k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} {μ[α]γ = μ[α]γ} ._ ._ c₁ c₂
              (Frame {μ[μ₄]μ₃ = μ[μ₄]μ₃} (App₁ e₂) {p₁} {p₂} same)
              e k₁ tr sch sch' =
  begin
    (cpsTerm {μs = μ[β]γ} (pcontext-plug (Frame (App₁ e₂) p₁) e) k₁ tr)
  ≡⟨ refl ⟩
      (cpsTerm (pcontext-plug p₁ e)
       (λ v₁ →
          cpsTerm e₂
          (λ v₂ t₃ →
             CPSApp
             (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
              (CPSVal
               (CPSFun
                (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
             (CPSVal t₃)))
       tr)
  ⟶⟨ control-lemma p₁ p₂ c₁ c₂ same e _ tr
        (λ v t → kSubst e₂ (λ v₂ t₂ → sApp (sApp (sApp (sVal sVar=) Subst≠)
                                                  Subst≠)
                                            Subst≠))
        (λ t v → tSubst e₂ (λ t₂ v₂ → sApp Subst≠ (sVal sVar=))) ⟩
    cpsTerm {μs = μ[μ₄]μ₃}
      (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) e)
      (λ v₁ →
         cpsTerm e₂
         (λ v₂ t₃ →
            CPSApp
            (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
            (CPSVal t₃)))
      tr
--------------------------------------------------------------------------- 1
  ⟶⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → begin
    (CPSApp
     (CPSApp
      (CPSApp
       (CPSVal (cpsV (Fun (λ x → pcontext-plug p₂ (Val (Var x))))))
       (CPSVal (cpsV v)))
      (CPSVal
       (CPSFun
        (λ v₁ →
           CPSVal
           (CPSFun
            (λ t'' →
               cpsTerm e₂
               (λ v₂ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                   (CPSVal
                    (CPSFun
                     (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                  (CPSVal t₃))
               (CPSVar t'')))))))
     (CPSVal t))
   ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
         eSubst (subst-context p₂ v)
           (λ sub-v₁ → sApp (sApp Subst≠ (sVal sub-v₁)) Subst≠)))))))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                cpsTerm (pcontext-plug p₂ (Val v))
                (λ v₁ t'' →
                   CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v₁)) (CPSVal t''))
                (CPSVar z₁))))))
       (CPSVal
        (CPSFun
         (λ v₁ →
            CPSVal
            (CPSFun
             (λ t'' →
                cpsTerm e₂
                (λ v₂ t₃ →
                   CPSApp
                   (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                    (CPSVal
                     (CPSFun
                      (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                   (CPSVal t₃))
                (CPSVar t'')))))))
      (CPSVal t)
   ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ t →
         kSubst (pcontext-plug p₂ (Val v))
           (λ v₂ t₂ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           cpsTerm (pcontext-plug p₂ (Val v))
           (λ z₁ z₂ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v₁ →
                    CPSVal
                    (CPSFun
                     (λ t'' →
                        cpsTerm e₂
                        (λ v₂ t₃ →
                           CPSApp
                           (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                            (CPSVal
                             (CPSFun
                              (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                           (CPSVal t₃))
                        (CPSVar t''))))))
               (CPSVal z₁))
              (CPSVal z₂))
           (CPSVar z))))
      (CPSVal t)
   ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v))
          (λ t₂ v₂ → sApp Subst≠ (sVal sVar=))) ⟩
    cpsTerm (pcontext-plug p₂ (Val v))
      (λ z₁ z₂ →
         CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ v₁ →
               CPSVal
               (CPSFun
                (λ t'' →
                   cpsTerm e₂
                   (λ v₂ t₃ →
                      CPSApp
                      (CPSApp (CPSApp (CPSVal (CPSVar v₁)) (CPSVal v₂))
                       (CPSVal
                        (CPSFun
                         (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                      (CPSVal t₃))
                   (CPSVar t''))))))
          (CPSVal z₁))
         (CPSVal z₂))
      t
--------------------------------------------------------------------------- 2
   ⟶⟨ correctCont (pcontext-plug p₂ (Val v)) _
         (λ v₁ t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v₁ t₁ → begin
    (CPSApp
     (CPSApp
      (CPSVal
       (CPSFun
        (λ v₂ →
           CPSVal
           (CPSFun
            (λ t'' →
               cpsTerm e₂
               (λ v₃ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal (CPSVar v₂)) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                  (CPSVal t₃))
               (CPSVar t''))))))
      (CPSVal (cpsV v₁)))
     (CPSVal t₁))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst e₂
          {k = (λ v₂ v₃ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal v₂) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                  (CPSVal t₃))}
          (λ x₁ t₄ →
            sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))))) ⟩
    (CPSApp (CPSVal
           (CPSFun
            (λ t'' →
               cpsTerm e₂
               (λ v₃ t₃ →
                  CPSApp
                  (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₃))
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
                  (CPSVal t₃))
               (CPSVar t''))))
     (CPSVal t₁))
    ⟶⟨ rBeta (tSubst e₂ (λ t₄ v₂ →
          sApp Subst≠ (sVal sVar=))) ⟩
     cpsTerm e₂
       (λ v₃ t₃ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₃))
           (CPSVal
            (CPSFun
             (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
          (CPSVal t₃))
       t₁
--------------------------------------------------------------------------- 3
    ⟶⟨ correctCont e₂ _
          (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
          (λ v₂ t₂ → begin
    (CPSApp
     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
      (CPSVal
       (CPSFun
        (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t''')))))))
     (CPSVal t₂))
   ⟵⟨ rApp₁ (rApp₂ (rFun (λ x → rFun (λ x₁ → rBeta
         (sch' (CPSVar x₁) (CPSVar x)))))) ⟩
    CPSApp
      (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSApp (CPSVal (CPSFun (λ z₂ → k₁ (CPSVar z) (CPSVar z₂))))
                (CPSVal (CPSVar z₁))))))))
      (CPSVal t₂)
   ⟵⟨ rApp₁ (rApp₂ (rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta
         (sVal (sFun (λ x₂ → sch (CPSVar x) (CPSVar x₂))))))))) ⟩
    (CPSApp
     (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
      (CPSVal
       (CPSFun
        (λ v₃ →
           CPSVal
           (CPSFun
            (λ t'' →
               CPSApp
               (CPSApp
                (CPSVal
                 (CPSFun
                  (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                (CPSVal (CPSVar v₃)))
               (CPSVal (CPSVar t''))))))))
     (CPSVal t₂))
    ∎) ⟩
--------------------------------------------------------------------------- 3
    (cpsTerm e₂
     (λ v₂ t₃ →
        CPSApp
        (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
         (CPSVal
          (CPSFun
           (λ v₃ →
              CPSVal
              (CPSFun
               (λ t'' →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                   (CPSVal (CPSVar v₃)))
                  (CPSVal (CPSVar t''))))))))
        (CPSVal t₃))
     t₁)
    ∎) ⟩
--------------------------------------------------------------------------- 2
    cpsTerm (pcontext-plug p₂ (Val v))
      (λ z z₁ →
         cpsTerm e₂
         (λ v₂ t₃ →
            CPSApp
            (CPSApp (CPSApp (CPSVal z) (CPSVal v₂))
             (CPSVal
              (CPSFun
               (λ v₃ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp
                      (CPSApp
                       (CPSVal
                        (CPSFun
                         (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                       (CPSVal (CPSVar v₃)))
                      (CPSVal (CPSVar t''))))))))
            (CPSVal t₃))
         z₁)
      t
   ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v))
         (λ t₃ v₂ → tSubst e₂ (λ t₄ v₃ →
         sApp Subst≠ (sVal sVar=)))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           cpsTerm (pcontext-plug p₂ (Val v))
           (λ v₁ →
              cpsTerm e₂
              (λ v₂ t₃ →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                  (CPSVal
                   (CPSFun
                    (λ v₃ →
                       CPSVal
                       (CPSFun
                        (λ t'' →
                           CPSApp
                           (CPSApp
                            (CPSVal
                             (CPSFun
                              (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                            (CPSVal (CPSVar v₃)))
                           (CPSVal (CPSVar t''))))))))
                 (CPSVal t₃)))
           (CPSVar z))))
      (CPSVal t)
   ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
         kSubst (pcontext-plug p₂ (Val v)) (λ x₁ t₁ →
           kSubst e₂ {k = λ x₂ v₂ t₄ →
                            CPSApp
                            (CPSApp (CPSApp (CPSVal x₁) (CPSVal v₂))
                             (CPSVal
                              (CPSFun
                               (λ v₃ →
                                  CPSVal
                                  (CPSFun
                                   (λ t'' →
                                      CPSApp (CPSApp (CPSVal x₂) (CPSVal (CPSVar v₃)))
                                      (CPSVal (CPSVar t''))))))))
                            (CPSVal t₄)}
                         (λ x₂ t₄ →
         sApp (sApp Subst≠ (sVal (sFun (λ x₃ → sVal (sFun (λ x₄ →
           sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠)))))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                cpsTerm (pcontext-plug p₂ (Val v))
                (λ v₁ →
                   cpsTerm e₂
                   (λ v₂ t₂ →
                      CPSApp
                      (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                       (CPSVal
                        (CPSFun
                         (λ v₃ →
                            CPSVal
                            (CPSFun
                             (λ t'' →
                                CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                                (CPSVal (CPSVar t''))))))))
                      (CPSVal t₂)))
                (CPSVar z₁))))))
       (CPSVal
        (CPSFun
         (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
      (CPSVal t)
   ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
         eSubst (subst-context p₂ v)
           (λ x₂ → kSubst′′ e₂ (λ sub →
             sApp (sApp (sApp (sVal x₂) (sVal sub)) Subst≠) Subst≠))))))))) ⟩
    (CPSApp
     (CPSApp
      (CPSApp
       (CPSVal
        (cpsV (Fun {μs = μ[α]γ} (λ x →
                App (pcontext-plug p₂ (Val (Var x))) e₂))))
       (CPSVal (cpsV v)))
      (CPSVal
       (CPSFun
        (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
     (CPSVal t))
   ∎)⟩
--------------------------------------------------------------------------- 1
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val (Fun (λ x → App (pcontext-plug p₂ (Val (Var x))) e₂)))
      e)
     k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val
       (Fun (λ x → pcontext-plug (Frame (App₁ e₂) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} ._ ._ c₁ c₂
              (Frame {μ[μ₄]μ₃ = μ[μ₄]μ₃} (App₂ v₁) {p₁} {p₂} same)
              e k₁ tr sch sch' =
  begin
    (cpsTerm (pcontext-plug (Frame (App₂ v₁) p₁) e) k₁ tr)
  ≡⟨ refl ⟩
      (cpsTerm (pcontext-plug p₁ e)
       (λ v₂ t₃ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
          (CPSVal t₃))
       tr)
  ⟶⟨ control-lemma p₁ p₂ c₁ c₂ same e _ tr
        (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ t₂ v₂ → sApp Subst≠ (sVal sVar=)) ⟩
    cpsTerm {μs = μ[μ₄]μ₃}
      (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) e)
      (λ v₂ t₃ →
         CPSApp
         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
          (CPSVal
           (CPSFun
            (λ v → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v) (CPSVar t'')))))))
         (CPSVal t₃))
      tr
---------------------------------------------------------------------- 1 start
  ⟵⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → begin
    (CPSApp
     (CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
             (λ x →
                CPSVal
                (CPSFun
                 (λ k' →
                    CPSVal
                    (CPSFun
                     (λ t' →
                        cpsTerm (pcontext-plug p₂ (Val (Var x)))
                        (λ v₂ t₃ →
                           CPSApp
                           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (CPSVal
                             (CPSFun
                              (λ v →
                                 CPSVal
                                 (CPSFun
                                  (λ t'' →
                                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v)))
                                     (CPSVal (CPSVar t''))))))))
                           (CPSVal t₃))
                        (CPSVar t'))))))))
       (CPSVal (cpsV v)))
      (CPSVal
       (CPSFun
        (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
     (CPSVal t))
   ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
         eSubst (subst-context p₂ v)
           (λ x₂ → sApp (sApp (sApp Subst≠ (sVal x₂)) Subst≠) Subst≠)))))))) ⟩
     CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSVal
             (CPSFun
              (λ z₁ →
                 cpsTerm (pcontext-plug p₂ (Val v))
                 (λ v₂ t₂ →
                    CPSApp
                    (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                     (CPSVal
                      (CPSFun
                       (λ v₃ →
                          CPSVal
                          (CPSFun
                           (λ t'' →
                              CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                              (CPSVal (CPSVar t''))))))))
                    (CPSVal t₂))
                 (CPSVar z₁))))))
        (CPSVal
         (CPSFun
          (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
       (CPSVal t)
   ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
         kSubst (pcontext-plug p₂ (Val v))
         {k = (λ y v₂ t₂ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t'' →
                    CPSApp (CPSApp (CPSVal y) (CPSVal (CPSVar v₃)))
                    (CPSVal (CPSVar t''))))))))
          (CPSVal t₂))} (λ x₁ t₃ →
         sApp (sApp Subst≠ (sVal (sFun (λ x₂ → sVal (sFun (λ x₃ →
           sApp (sApp (sVal sVar=) Subst≠) Subst≠)))))) Subst≠)
         )))) ⟩
     CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ v₂ t₂ →
               CPSApp
               (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                (CPSVal
                 (CPSFun
                  (λ v₃ →
                     CPSVal
                     (CPSFun
                      (λ t'' →
                         CPSApp
                         (CPSApp
                          (CPSVal
                           (CPSFun
                            (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                          (CPSVal (CPSVar v₃)))
                         (CPSVal (CPSVar t''))))))))
               (CPSVal t₂))
            (CPSVar z))))
       (CPSVal t)
   ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
         sApp Subst≠ (sVal sVar=))) ⟩
     cpsTerm (pcontext-plug p₂ (Val v))
       (λ v₂ t₂ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t'' →
                    CPSApp
                    (CPSApp
                     (CPSVal
                      (CPSFun
                       (λ v₄ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₄) (CPSVar t'''))))))
                     (CPSVal (CPSVar v₃)))
                    (CPSVal (CPSVar t''))))))))
          (CPSVal t₂))
       t
   ⟶⟨ correctCont (pcontext-plug p₂ (Val v)) _
         (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
         (λ v₂ t₂ → rApp₁ (rApp₂ (rFun (λ x → rFun (λ x₁ →
           rApp₁ (rBeta (sVal (sFun (λ x₂ →
             sch (CPSVar x) (CPSVar x₂)))))))))) ⟩
     cpsTerm (pcontext-plug p₂ (Val v))
       (λ v₂ t₂ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t'' →
                    CPSApp
                    (CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t'''))))
                    (CPSVal (CPSVar t''))))))))
          (CPSVal t₂))
       t
   ⟶⟨ correctCont (pcontext-plug p₂ (Val v)) _
         (λ v₂ t₂ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
         (λ v₂ t₂ → rApp₁ (rApp₂ (rFun (λ x → rFun (λ x₁ →
           rBeta (sch' (CPSVar x₁) (CPSVar x))))))) ⟩
     cpsTerm (pcontext-plug p₂ (Val v))
       (λ v₂ t₂ →
          CPSApp
          (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t'' →
                    k₁ (CPSVar v₃) (CPSVar t'')))))))
          (CPSVal t₂))
       t
---------------------------------------------------------------------- 2 start
   ⟵⟨ correctCont (pcontext-plug p₂ (Val v)) _
         (λ v₂ t₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
         (λ v₂ t₂ → begin
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₃ →
             CPSVal
             (CPSFun
              (λ t''' →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                  (CPSVal
                   (CPSFun
                    (λ v₄ →
                       CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                 (CPSVal (CPSVar t''')))))))
        (CPSVal (cpsV v₂)))
       (CPSVal t₂))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x → sApp (sApp (sApp Subst≠ (sVal sVar=))
                                                    Subst≠)
                                              Subst≠)))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSApp
             (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
              (CPSVal
               (CPSFun
                (λ v₄ →
                   CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
             (CPSVal (CPSVar z)))))
        (CPSVal t₂)
    ⟶⟨ rBeta (sApp Subst≠ (sVal sVar=)) ⟩
      (CPSApp
       (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
        (CPSVal
         (CPSFun
          (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₃) (CPSVar t'')))))))
       (CPSVal t₂))
    ∎) ⟩
---------------------------------------------------------------------- 2 end
     cpsTerm (pcontext-plug p₂ (Val v))
       (λ v₂ t'' →
          CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ v₃ →
                CPSVal
                (CPSFun
                 (λ t''' →
                    CPSApp
                    (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                     (CPSVal
                      (CPSFun
                       (λ v₄ →
                          CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                    (CPSVal (CPSVar t''')))))))
           (CPSVal v₂))
          (CPSVal t''))
       t
   ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
         sApp Subst≠ (sVal sVar=))) ⟩
     CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ v₂ t'' →
               CPSApp
               (CPSApp
                (CPSVal
                 (CPSFun
                  (λ v₃ →
                     CPSVal
                     (CPSFun
                      (λ t''' →
                         CPSApp
                         (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                          (CPSVal
                           (CPSFun
                            (λ v₄ →
                               CPSVal (CPSFun (λ t'''' → k₁ (CPSVar v₄) (CPSVar t'''')))))))
                         (CPSVal (CPSVar t''')))))))
                (CPSVal v₂))
               (CPSVal t''))
            (CPSVar z))))
       (CPSVal t)
   ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
         kSubst (pcontext-plug p₂ (Val v))
         {k = (λ y v₂ t'' →
          CPSApp (CPSApp (CPSVal y) (CPSVal v₂)) (CPSVal t''))}
         (λ x₁ t₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)
         )))) ⟩
     CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSVal
             (CPSFun
              (λ z₁ →
                 cpsTerm (pcontext-plug p₂ (Val v))
                 (λ v₂ t'' →
                    CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v₂)) (CPSVal t''))
                 (CPSVar z₁))))))
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                  (CPSVal
                   (CPSFun
                    (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                 (CPSVal (CPSVar t''))))))))
       (CPSVal t)
   ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
         eSubst (subst-context p₂ v) (λ x₂ →
           sApp (sApp Subst≠ (sVal x₂)) Subst≠)))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v₂)) (CPSVal t''))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSApp
                 (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                  (CPSVal
                   (CPSFun
                    (λ v₃ → CPSVal (CPSFun (λ t''' → k₁ (CPSVar v₃) (CPSVar t''')))))))
                 (CPSVal (CPSVar t''))))))))
       (CPSVal t))
   ∎) ⟩
---------------------------------------------------------------------- 1 end
      cpsTerm e
      (λ z z₁ →
         CPSApp
         (CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ x →
                CPSVal
                (CPSFun
                 (λ k' →
                    CPSVal
                    (CPSFun
                     (λ t' →
                        cpsTerm (pcontext-plug p₂ (Val (Var x)))
                        (λ v₂ t₃ →
                           CPSApp
                           (CPSApp (CPSApp (CPSVal (cpsV v₁)) (CPSVal v₂))
                            (CPSVal
                             (CPSFun
                              (λ v →
                                 CPSVal
                                 (CPSFun
                                  (λ t'' →
                                     CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v)))
                                     (CPSVal (CPSVar t''))))))))
                           (CPSVal t₃))
                        (CPSVar t'))))))))
           (CPSVal z))
          (CPSVal
           (CPSFun
            (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
         (CPSVal z₁))
      tr
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[β]γ}
      (Val
       (Fun (λ x → App (Val v₁) (pcontext-plug p₂ (Val (Var x))))))
      e)
     k₁ tr)
  ≡⟨ refl ⟩
    (cpsTerm {μs = μ[β]γ}
     (App
      (Val
       (Fun (λ x → pcontext-plug (Frame (App₂ v₁) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} {μ[α]γ} ._ ._ c₁ c₂
              (Frame (Plus₁ e₂) {p₁} {p₂} same) e k₁ tr sch sch' =
  begin
    (cpsTerm {μs = μ[β]γ}
             (pcontext-plug (Frame (Plus₁ e₂) p₁) e) k₁ tr)
  ⟶⟨ control-lemma p₁ p₂ c₁ c₂ same e _ tr
         (λ v₂ t₂ → kSubst e₂
                    {k = (λ x v₃ t₄ →
                           CPSLet (CPSPlus (CPSVal x) (CPSVal v₃))
                           (λ v → k₁ (CPSVar v) t₄))}
                    λ x t → sLet (λ n → Subst≠)
                                 (λ n → sPlu (sVal sVar=) Subst≠))
         (λ t₂ v₂ → tSubst e₂ (λ t v₃ →
           sLet (λ n → sch' t (CPSVar n))
                (λ n → Subst≠))) ⟩
      cpsTerm e
      (λ v₂ t₃ →
         CPSApp
         (CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ x →
                CPSVal
                (CPSFun
                 (λ k' →
                    CPSVal
                    (CPSFun
                     (λ t' →
                        cpsTerm (pcontext-plug p₂ (Val (Var x)))
                        (λ v t'' →
                           CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                        (CPSVar t'))))))))
           (CPSVal v₂))
          (CPSVal
           (CPSFun
            (λ v →
               CPSVal
               (CPSFun
                (λ t'' →
                   cpsTerm e₂
                   (λ v₃ t₄ →
                      CPSLet (CPSPlus (CPSVal (CPSVar v)) (CPSVal v₃))
                      (λ v₁ → k₁ (CPSVar v₁) t₄))
                   (CPSVar t'')))))))
         (CPSVal t₃))
      tr
---------------------------------------------------------------------- 1 start
  ⟶⟨ correctCont e _
        (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
        (λ v t → rApp₁ (
    begin
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v₁ t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v₁)) (CPSVal t''))
                     (CPSVar t'))))))))
        (CPSVal (cpsV v)))
       (CPSVal
        (CPSFun
         (λ v₁ →
            CPSVal
            (CPSFun
             (λ t'' →
                cpsTerm e₂
                (λ v₃ t₄ →
                   CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₃))
                   (λ v₂ → k₁ (CPSVar v₂) t₄))
                (CPSVar t'')))))))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
          eSubst (subst-context p₂ v) (λ x₂ →
            sApp (sApp Subst≠ (sVal x₂)) Subst≠))))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSVal
             (CPSFun
              (λ z₁ →
                 cpsTerm (pcontext-plug p₂ (Val v))
                 (λ v₁ t'' →
                    CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v₁)) (CPSVal t''))
                 (CPSVar z₁))))))
        (CPSVal
         (CPSFun
          (λ v₁ →
             CPSVal
             (CPSFun
              (λ t'' →
                 cpsTerm e₂
                 (λ v₃ t₄ →
                    CPSLet (CPSPlus (CPSVal (CPSVar v₁)) (CPSVal v₃))
                    (λ v₂ → k₁ (CPSVar v₂) t₄))
                 (CPSVar t''))))))
    ⟶⟨ rBeta (sVal (sFun (λ x →
          kSubst (pcontext-plug p₂ (Val v))
            {k = λ y v₁ t'' →
                   CPSApp (CPSApp (CPSVal y) (CPSVal v₁)) (CPSVal t'')}
            (λ x₁ t₃ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)))) ⟩
      CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ v₁ t'' →
               CPSApp
               (CPSApp
                (CPSVal
                 (CPSFun
                  (λ v₂ →
                     CPSVal
                     (CPSFun
                      (λ t''' →
                         cpsTerm e₂
                         (λ v₃ t₄ →
                            CPSLet (CPSPlus (CPSVal (CPSVar v₂)) (CPSVal v₃))
                            (λ v₄ → k₁ (CPSVar v₄) t₄))
                         (CPSVar t'''))))))
                (CPSVal v₁))
               (CPSVal t''))
            (CPSVar z)))
    ⟶⟨ rFun (λ x → correctCont (pcontext-plug p₂ (Val v)) _ (λ v₃ t₃ →
           sApp (sApp Subst≠ (sVal sVar=)) Subst≠) (λ v₃ t₃ →
             rApp₁ (rBeta (sVal (sFun (λ x₁ → kSubst′′ e₂ (λ x₂ →
               sLet (λ x₃ → Subst≠)
                    (λ x₃ → sPlu (sVal sVar=) (sVal x₂))))))))) ⟩
      CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ v₁ t'' →
               CPSApp (CPSVal
                     (CPSFun
                      (λ t''' →
                         cpsTerm e₂
                         (λ v₃ t₄ →
                            CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                            (λ v₄ → k₁ (CPSVar v₄) t₄))
                         (CPSVar t'''))))
               (CPSVal t''))
            (CPSVar z)))
    ⟶⟨ rFun (λ x → correctCont (pcontext-plug p₂ (Val v)) _
          (λ v₁ t₃ → sApp (sVal (sFun (λ x₁ →
                             kSubst′′ e₂ (λ x₂ → sLet (λ x₃ → Subst≠)
                               (λ x₃ → sPlu (sVal sVar=) (sVal x₂))))))
                          Subst≠)
          (λ v₁ t₃ → rBeta (tSubst e₂ (λ t₄ v₂ →
                       sLet (λ x₁ → sch' t₄ (CPSVar x₁))
                            (λ x₁ → Subst≠))))) ⟩
      CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ v₁ t'' →
                         cpsTerm e₂
                         (λ v₃ t₄ →
                            CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₃))
                            (λ v₄ → k₁ (CPSVar v₄) t₄))
                         t'')
            (CPSVar z)))
    ⟵⟨ rFun (λ x → correctCont (pcontext-plug p₂ (Val v)) _
          (λ v₁ t₃ → kSubst′′ e₂ (λ x₁ →
            sLet (λ x₂ → Subst≠) (λ x₂ → sPlu (sVal sVar=) (sVal x₁))))
          (λ v₁ t₃ → correctCont e₂ _
            (λ v₂ t₄ → sLet (λ x₁ → sApp Subst≠ Subst≠)
                            (λ x₁ → sPlu Subst≠ (sVal sVar=)))
            (λ v₂ t₄ → rLet₂ (λ x₁ → rBeta (sch' t₄ (CPSVar x₁)))))) ⟩
      CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ z₁ z₂ →
               cpsTerm e₂
               (λ v₁ v₂ →
                  CPSLet (CPSPlus (CPSVal z₁) (CPSVal v₁))
                  (λ v₃ →
                     CPSApp
                     (CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₃) (CPSVar t''))))
                     (CPSVal v₂)))
               z₂)
            (CPSVar z)))
    ⟵⟨ rFun (λ x → correctCont (pcontext-plug p₂ (Val v)) _
          (λ v₁ t₃ → kSubst′′ e₂ (λ x₁ → sLet (λ x₂ → sApp Subst≠ Subst≠)
                                               (λ x₂ → sPlu (sVal sVar=)
                                                            (sVal x₁))))
          (λ v₁ t₃ → correctCont e₂ _
            (λ v₂ t₄ → sLet (λ x₁ → Subst≠)
                            (λ x₁ → sPlu Subst≠ (sVal sVar=)))
            (λ v₂ t₄ → rLet₂ (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ →
                             sch (CPSVar x₁) (CPSVar x₂))))))))) ⟩
      CPSVal
        (CPSFun
         (λ z →
            cpsTerm (pcontext-plug p₂ (Val v))
            (λ z₁ z₂ →
               cpsTerm e₂
               (λ v₁ v₂ →
                  CPSLet (CPSPlus (CPSVal z₁) (CPSVal v₁))
                  (λ v₃ →
                     CPSApp
                     (CPSApp
                      (CPSVal
                       (CPSFun
                        (λ v₄ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₄) (CPSVar t''))))))
                      (CPSVal (CPSVar v₃)))
                     (CPSVal v₂)))
               z₂)
            (CPSVar z)))
    ⟵⟨ rBeta (sVal (sFun (λ x → kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
          kSubst′′ e₂ (λ x₂ →
            sLet (λ n → sApp (sApp (sVal sVar=) Subst≠) Subst≠)
                 (λ n → sPlu (sVal x₁) (sVal x₂))))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSVal
             (CPSFun
              (λ z₁ →
                 cpsTerm (pcontext-plug p₂ (Val v))
                 (λ z₂ z₃ →
                    cpsTerm e₂
                    (λ v₁ v₂ →
                       CPSLet (CPSPlus (CPSVal z₂) (CPSVal v₁))
                       (λ v₃ →
                          CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                          (CPSVal v₂)))
                    z₃)
                 (CPSVar z₁))))))
        (CPSVal
         (CPSFun
          (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t''))))))
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
          eSubst (subst-context p₂ v) (λ x₂ →
            kSubst′′ e₂ (λ x₃ →
              sLet (λ n → sApp Subst≠ Subst≠)
                   (λ n → sPlu (sVal x₂) (sVal x₃)))))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v₁ →
                        cpsTerm e₂
                        (λ v₂ t₃ →
                           CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
                           (λ v₃ →
                              CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v₃)))
                              (CPSVal t₃))))
                     (CPSVar t'))))))))
        (CPSVal (cpsV v)))
       (CPSVal
        (CPSFun
         (λ v₁ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₁) (CPSVar t'')))))))
    ∎)) ⟩
---------------------------------------------------------------------- 1 end
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val
       (Fun (λ x → pcontext-plug (Frame (Plus₁ e₂) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

control-lemma {μ[β]γ = μ[β]γ} {μ[α]γ} .(Frame (Plus₂ v₁) p₁) .(Frame (Plus₂ v₁) p₂) c₁ c₂ (Frame (Plus₂ v₁) {p₁} {p₂} same) e k₁ tr sch sch' =
  begin
    (cpsTerm {μs = μ[β]γ}
             (pcontext-plug (Frame (Plus₂ v₁) p₁) e) k₁ tr)
  ⟶⟨ control-lemma p₁ p₂ c₁ c₂ same e _ tr
        (λ v₂ t₂ → sLet (λ x → Subst≠) (λ x → sPlu Subst≠ (sVal sVar=)))
        (λ t₂ v₂ → sLet (λ x → sch' t₂ (CPSVar x)) (λ x → Subst≠)) ⟩
    cpsTerm {μs = μ[β]γ}
      (App (Val (Fun (λ x → pcontext-plug p₂ (Val (Var x))))) e)
      (λ v₂ t₂ →
         CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
         (λ v → k₁ (CPSVar v) t₂))
      tr
---------------------------------------------------------------------- 1 start
  ⟶⟨ correctCont e _
      (λ v t → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
      (λ v t →
    begin
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v₂)) (CPSVal t''))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                 (λ v₃ → k₁ (CPSVar v₃) (CPSVar t''))))))))
       (CPSVal t))
    ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
          eSubst (subst-context p₂ v) (λ x₂ →
            sApp (sApp Subst≠ (sVal x₂)) Subst≠)))))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ v₂ t'' →
                     CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v₂)) (CPSVal t''))
                  (CPSVar z₁))))))
         (CPSVal
          (CPSFun
           (λ v₂ →
              CPSVal
              (CPSFun
               (λ t'' →
                  CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                  (λ v₃ → k₁ (CPSVar v₃) (CPSVar t''))))))))
        (CPSVal t)
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
            sApp (sApp (sVal sVar=) (sVal x₁)) Subst≠))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             cpsTerm (pcontext-plug p₂ (Val v))
             (λ z₁ z₂ →
                CPSApp
                (CPSApp
                 (CPSVal
                  (CPSFun
                   (λ v₂ →
                      CPSVal
                      (CPSFun
                       (λ t'' →
                          CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                          (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'')))))))
                 (CPSVal z₁))
                (CPSVal z₂))
             (CPSVar z))))
        (CPSVal t)
    ⟶⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
          sApp Subst≠ (sVal sVar=))) ⟩
      cpsTerm (pcontext-plug p₂ (Val v))
        (λ z₁ z₂ →
           CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₂ →
                 CPSVal
                 (CPSFun
                  (λ t'' →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₂)))
                     (λ v₃ → k₁ (CPSVar v₃) (CPSVar t'')))))))
            (CPSVal z₁))
           (CPSVal z₂))
        t
---------------------------------------------------------------------- 2 start
    ⟶⟨ correctCont (pcontext-plug p₂ (Val v)) _
        (λ v₂ t₃ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v₂ t₃ →
    begin
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ v₃ →
             CPSVal
             (CPSFun
              (λ t'' →
                 CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (CPSVar v₃)))
                 (λ v₄ → k₁ (CPSVar v₄) (CPSVar t'')))))))
        (CPSVal (cpsV v₂)))
       (CPSVal t₃))
    ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          sLet (λ x₁ → Subst≠) (λ x₁ → sPlu Subst≠ (sVal sVar=)))))) ⟩
      CPSApp
        (CPSVal
         (CPSFun
          (λ z →
             CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
             (λ z₁ → k₁ (CPSVar z₁) (CPSVar z)))))
        (CPSVal t₃)
    ⟶⟨ rBeta (sLet (λ x → sch' t₃ (CPSVar x)) (λ x → Subst≠)) ⟩
      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
        (λ z → k₁ (CPSVar z) t₃)
    ⟵⟨ rLet₂ (λ x → rBeta (sch' t₃ (CPSVar x))) ⟩
      CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
        (λ z →
           CPSApp (CPSVal (CPSFun (λ z₁ → k₁ (CPSVar z) (CPSVar z₁))))
           (CPSVal t₃))
    ⟵⟨ rLet₂ (λ x → rApp₁ (rBeta (sVal (sFun (λ x₁ →
          sch (CPSVar x) (CPSVar x₁)))))) ⟩
      (CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal (cpsV v₂)))
       (λ z₂ →
          CPSApp
          (CPSApp
           (CPSVal
            (CPSFun
             (λ v₃ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₃) (CPSVar t''))))))
           (CPSVal (CPSVar z₂)))
          (CPSVal t₃)))
    ∎) ⟩
---------------------------------------------------------------------- 2 end
      cpsTerm (pcontext-plug p₂ (Val v))
        (λ z z₁ →
           CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal z))
           (λ z₂ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t''))))))
               (CPSVal (CPSVar z₂)))
              (CPSVal z₁)))
        t
    ⟵⟨ rBeta (tSubst (pcontext-plug p₂ (Val v)) (λ t₃ v₂ →
          sLet (λ x → sApp Subst≠ (sVal sVar=)) (λ x → Subst≠))) ⟩
      CPSApp (CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ v₂ t₃ →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                     (λ v₃ →
                        CPSApp (CPSApp (CPSVal (CPSFun
           (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))) (CPSVal (CPSVar v₃)))
                        (CPSVal t₃)))
                  (CPSVar z₁))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
          kSubst′′ (pcontext-plug p₂ (Val v)) (λ x₁ →
            sLet (λ x₂ → sApp (sApp (sVal sVar=) Subst≠) Subst≠)
                 (λ x₂ → sPlu Subst≠ (sVal x₁))))))) ⟩
      CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ z →
              CPSVal
              (CPSFun
               (λ z₁ →
                  cpsTerm (pcontext-plug p₂ (Val v))
                  (λ v₂ t₃ →
                     CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                     (λ v₃ →
                        CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal (CPSVar v₃)))
                        (CPSVal t₃)))
                  (CPSVar z₁))))))
         (CPSVal
          (CPSFun
           (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
        (CPSVal t)
    ⟵⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ x → sVal (sFun (λ x₁ →
          eSubst (subst-context p₂ v) (λ x₂ →
            sLet (λ x₃ → sApp Subst≠ Subst≠)
                 (λ x₃ → sPlu Subst≠ (sVal x₂)))))))))) ⟩
      (CPSApp
       (CPSApp
        (CPSApp
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v₂ t₃ →
                         CPSLet (CPSPlus (CPSVal (cpsV v₁)) (CPSVal v₂))
                         (λ v₃ →
                            CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal (CPSVar v₃)))
                            (CPSVal t₃)))
                      (CPSVar t'))))))))
         (CPSVal (cpsV v)))
        (CPSVal
         (CPSFun
          (λ v₂ → CPSVal (CPSFun (λ t'' → k₁ (CPSVar v₂) (CPSVar t'')))))))
       (CPSVal t))
    ∎) ⟩
---------------------------------------------------------------------- 1 end
    (cpsTerm {μs = μ[β]γ}
     (App {μ[β]α = μ[α]γ}
      (Val
       (Fun (λ x → pcontext-plug (Frame (Plus₂ v₁) p₂) (Val (Var x)))))
      e)
     k₁ tr)
  ∎

-- end of control lemma

{-

cons-assoc-2 : {var : cpstyp → Set} {τ α τ' α' τ₁ α₁ τ₂ α₂ : typ}
               {μk μt μkt μ μ' μ₀ : trail}
               (k : cpsvalue[ var ] cpsM (τ₂ ⇒ α₂ , μk))
               (t : cpsvalue[ var ] cpsM (τ₁ ⇒ α₁ , μt))
               (kt : cpsvalue[ var ] cpsM μkt)
               (c₁ : compatible (τ₂ ⇒ α₂ , μk) (τ₁ ⇒ α₁ , μt)
                                (τ ⇒ α , μ))
               (c₂ : compatible (τ ⇒ α , μ) μkt (τ' ⇒ α' , μ'))
               (c₁' : compatible (τ₁ ⇒ α₁ , μt) μkt μ₀)
               (c₂' : compatible (τ₂ ⇒ α₂ , μk) μ₀ (τ' ⇒ α' , μ')) →
               cpsreduce (CPSVal (CPSCons c₂ (CPSCons c₁ k t) kt))
                         (CPSVal (CPSCons c₂' k (CPSCons c₁' t kt)))

cons-assoc-2 {var} {τ} {α} {τ'} {α'} {τ₁} {α₁} {τ₂} {α₂} {μk} {μt} {∙} {μ} {μ'} {μ₀} k t kt (refl , refl , c₁) refl refl (refl , refl , c₂') rewrite compatible-equal c₁ c₂' = begin
  (CPSVal (CPSCons refl (CPSCons (refl , refl , c₂') k t) kt))
  ⟶⟨ rConsid₂ ⟩
  CPSVal (CPSCons (refl , refl , c₂') k t)
  ⟵⟨ rCon₂ rConsid₂ ⟩
  (CPSVal (CPSCons (refl , refl , c₂') k (CPSCons refl t kt)))
  ∎

cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {.(τ₁ ⇒ α₁ , ∙)} {.(τ₃ ⇒ τ'' , μkt)} {τ₃ ⇒ τ'' , μkt} {.(τ₃ ⇒ τ'' , μkt)} {∙} {τ₁ ⇒ α₁ , ∙} k t kt (refl , refl , refl , refl , refl) (refl , refl , refl) (refl , refl , refl) (refl , refl , refl) = begin
  (CPSVal
       (CPSCons (refl , refl , refl)
        (CPSCons (refl , refl , refl , refl , refl) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , refl , refl) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons (refl , refl , refl) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons refl kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal (CPSCons (refl , refl , refl) t (CPSVar z₂))))))
            (CPSVal (CPSCons refl kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , refl) t (CPSCons refl kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , refl) refl refl (refl , refl , refl)))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons refl (CPSCons (refl , refl , refl) t kt) (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl) k
        (CPSCons (refl , refl , refl) t kt)))
  ∎
cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {.(τ₁ ⇒ α₁ , (τ₂ ⇒ τ' , μ₀))} {τ₄ ⇒ τ''' , μt} {.τ₄ ⇒ .τ''' , μkt} {.(τ₄ ⇒ τ''' , μkt)} {∙} {τ₁ ⇒ α₁ , (τ₂ ⇒ τ' , μ₀)} k t kt (refl , refl , refl , refl , refl , refl , snd) (refl , refl , refl) (refl , refl , refl , refl , snd₁) (refl , refl , refl) = begin
  (CPSVal
       (CPSCons (refl , refl , refl)
        (CPSCons (refl , refl , refl , refl , refl , refl , snd) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , (refl , (refl , (refl , snd)))) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal
                       (CPSCons (refl , refl , refl , refl , snd) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons refl kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal
                  (CPSCons (refl , refl , refl , refl , snd) t (CPSVar z₂))))))
            (CPSVal (CPSCons refl kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , refl , refl , snd) t
              (CPSCons refl kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , refl , refl , snd₁)
                                           refl refl (refl , (refl , (refl , (refl , snd))))))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons refl (CPSCons (refl , refl , refl , refl , snd₁) t kt)
              (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl) k
        (CPSCons (refl , refl , refl , refl , snd₁) t kt)))
  ∎
    -- (CPSVal
    --                (CPSCons c₂
    --                  (CPSCons c₁ k t) kt))
    --              (CPSVal
    --                (CPSCons c₂' k
    --                  (CPSCons c₁' t kt)))
cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {τ₅ ⇒ τ'''' , μk} {μt} {τ₃ ⇒ τ'' , μkt} {τ₄ ⇒ τ''' , μ} {τ₂ ⇒ τ' , μ'} {τ₁ ⇒ α₁ , ∙} k t kt (refl , refl , refl , refl , c₁) (refl , refl , refl , refl , c₂) (refl , refl , refl) (refl , refl , refl , refl , c₂') = begin
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂)
        (CPSCons (refl , refl , refl , refl , c₁) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl , refl , c₂)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , (refl , c₁)) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons (refl , (refl , c₂)) kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar z₂))))))
            (CPSVal (CPSCons (refl , refl , c₂) kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , c₁) t
              (CPSCons (refl , refl , c₂) kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , refl)
                                           (refl , refl , c₂') (refl , (refl , c₂)) (refl , (refl , c₁))))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons (refl , (refl , c₂')) (CPSCons (refl , refl , refl) t kt) (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂') k
        (CPSCons (refl , refl , refl) t kt)))
  ∎
cons-assoc-2 {var} {τ} {α} {.τ} {.α} {τ₁} {α₁} {.τ} {.α} {τ₅ ⇒ τ'''' , μk} {μt} {τ₃ ⇒ τ'' , μkt} {τ₇ ⇒ τ'''''' , μ} {τ₂ ⇒ τ' , μ'} {τ₁ ⇒ α₁ , (τ₄ ⇒ τ''' , μ₀)} k t kt (refl , refl , refl , refl , c₁) (refl , refl , refl , refl , c₂) (refl , refl , c₁') (refl , refl , refl , refl , c₂') = begin
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂)
        (CPSCons (refl , refl , refl , refl , c₁) k t) kt))
  ⟶⟨ rCon₁ rConst ⟩
  CPSVal
    (CPSCons (refl , refl , refl , refl , c₂)
     (CPSFun
      (λ v →
         CPSVal
         (CPSFun
          (λ t' →
             CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
             (CPSVal (CPSCons (refl , (refl , c₁)) t (CPSVar t')))))))
     kt)
  ⟶⟨ rConst ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp
            (CPSApp
             (CPSVal
              (CPSFun
               (λ v₁ →
                  CPSVal
                  (CPSFun
                   (λ t'' →
                      CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v₁)))
                      (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar t''))))))))
             (CPSVal (CPSVar v)))
            (CPSVal (CPSCons (refl , (refl , c₂)) kt (CPSVar t')))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp
            (CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
                 (CPSVal (CPSCons (refl , refl , c₁) t (CPSVar z₂))))))
            (CPSVal (CPSCons (refl , refl , c₂) kt (CPSVar z₁)))))))
  ⟶⟨ rFun (λ x → rFun (λ x₁ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))) ⟩
  CPSVal
    (CPSFun
     (λ z →
        CPSVal
        (CPSFun
         (λ z₁ →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar z)))
            (CPSVal
             (CPSCons (refl , refl , c₁) t
              (CPSCons (refl , refl , c₂) kt (CPSVar z₁))))))))
  ⟵⟨ rFun (λ x → rFun (λ x₁ → rApp₂ (cons-assoc-2 t kt (CPSVar x₁) (refl , refl , c₁')
                                           (refl , refl , c₂') (refl , (refl , c₂)) (refl , (refl , c₁))))) ⟩
  CPSVal
    (CPSFun
     (λ v →
        CPSVal
        (CPSFun
         (λ t' →
            CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
            (CPSVal
             (CPSCons (refl , (refl , c₂')) (CPSCons (refl , refl , c₁') t kt) (CPSVar t')))))))
  ⟵⟨ rConst ⟩
  (CPSVal
       (CPSCons (refl , refl , refl , refl , c₂') k
        (CPSCons (refl , refl , c₁') t kt)))
  ∎

--------------------------------------------------------------------------------------------------------------------------
assoc : ∀ {var : cpstyp → Set} {τ α : typ} {μα μβ μ₀ : trail}
       {μ[β]α : trails[ μβ ] μα}
       {c : compatible (τ ⇒ α , μα) μβ μβ}
       {c' : compatible (τ ⇒ α , μα) μα μα}
       {c₂ : compatible μβ μ₀ μα}
       (k : var (cpsT τ ⇛ (cpsMs μ[β]α ⇛ cpsT α)))
       (t : cpsvalue[ var ] cpsM μβ)
       (k't' : cpsvalue[ var ] cpsM μ₀) →
        cpsreduce
        (CPSVal (CPSAppend c₂ (CPSCons c (CPSVar k) t) k't'))
        (CPSVal (CPSCons c' (CPSVar k) (CPSAppend c₂ t k't')))

assoc {var} {τ} {α} {τ₁ ⇒ τ' , μα} {τ₂ ⇒ τ'' , μβ} {∙} {μ[β]α} {refl , refl , c} {refl , refl , c'} {refl} k t k't' rewrite compatible-equal c c' = begin
  (CPSVal
       (CPSAppend refl (CPSCons (refl , refl , c') (CPSVar k) t) k't'))
  ⟶⟨ rApdt ⟩
  CPSVal (CPSCons refl (CPSCons (refl , refl , c') (CPSVar k) t) k't')
  ⟶⟨ rConsid₂ ⟩
  CPSVal (CPSCons (refl , refl , c') (CPSVar k) t)
  ⟵⟨ rCon₂ rConsid₂ ⟩
  CPSVal
    (CPSCons (refl , refl , c') (CPSVar k) (CPSCons refl t k't'))
  ⟵⟨ rCon₂ rApdt ⟩
  (CPSVal
       (CPSCons (refl , refl , c') (CPSVar k) (CPSAppend refl t k't')))
  ∎
assoc {var} {τ} {α} {τ₁ ⇒ τ' , μα} {τ₂ ⇒ τ'' , μβ} {τ₃ ⇒ τ''' , μ₀} {μ[β]α} {refl , refl , c} {refl , refl , c'} {refl , refl , c₂} k t k't' = begin
  (CPSVal
       (CPSAppend (refl , refl , c₂)
        (CPSCons (refl , refl , c) (CPSVar k) t) k't'))
  ⟶⟨ rApdt ⟩
  CPSVal
    (CPSCons (refl , refl , c₂)
     (CPSCons (refl , refl , c) (CPSVar k) t) k't')
  ⟶⟨ cons-assoc-2 (CPSVar k) t k't' (refl , refl , c) (refl , refl , c₂)
       (refl , refl , c₂) (refl , refl , c') ⟩
  CPSVal
    (CPSCons (refl , refl , c') (CPSVar k)
     (CPSCons (refl , refl , c₂) t k't'))
  ⟵⟨ rCon₂ rApdt ⟩
  (CPSVal
       (CPSCons (refl , refl , c') (CPSVar k)
        (CPSAppend (refl , refl , c₂) t k't')))
  ∎
-}

--9/22--------------------------------------------------------------------
aux₄-s : {var : cpstyp → Set} {τ α β : typ} {μα μβ : trail}
         {μ[β]α : trails[ μβ ] μα} →
         (e : term[ var ∘ cpsT ] τ ⟨ μ[β]α ⟩ α ⟨ μβ ⟩ β)
         {c : compatible (τ ⇒ α , μα) μβ μβ}
         (κ : cpsvalue[ var ] (cpsT τ) → cpsvalue[ var ] (cpsM μα) →
               cpsterm[ var ] (cpsT α))
         (k : var (cpsT τ ⇛ (cpsMs μ[β]α ⇛ cpsT α)))
         (t : var (cpsM μβ))
         (c' : compatible (τ ⇒ α , μα) μα μα) →
         (sch : schematicV′ κ) →
         cpsreduce {var}
          (cpsTerm e (λ v t' → κ v t') (CPSCons c (CPSVar k) (CPSVar t)))
          (cpsTerm e (λ v t' → κ v (CPSCons c' (CPSVar k) t')) (CPSVar t))

aux₄-s = {!!}
{-
aux₄-s (Val v) κ k t c' sch = {!!}
aux₄-s (App e e₁) κ k t c' sch = {!!}
aux₄-s {μβ = τ ⇒ τ' , μβ} (Plus e e₁) κ k t c' sch = {!!}
aux₄-s {μ[β]α = μ[β]α} (Control id₁ c₁ c₂ e) {c} κ k t c' sch = begin
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSCons c (CPSVar k) (CPSVar t))
                      (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → κ (CPSVar v) (CPSVar t'')))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))

  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLetApp)))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSVal (CPSFun (λ t'' → κ (CPSVar z) (CPSVar t''))))
                 (CPSVal
                  (CPSAppend c₂ (CPSCons c (CPSVar k) (CPSVar t))
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rApp₂ (assoc {μ[β]α = μ[β]α} k (CPSVar t) (CPSCons c₁ (CPSVar x₁) (CPSVar x₂))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar z) (CPSVar x))))
                 (CPSVal
                  (CPSCons c' (CPSVar k)
                   (CPSAppend c₂ (CPSVar t)
                    (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ z₃ →
                      CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar z) (CPSVar x))))
                      (CPSVal (CPSCons c' (CPSVar k) (CPSVar z₃))))))
                 (CPSVal
                  (CPSAppend c₂ (CPSVar t)
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟶⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rApp₁ (rFun (λ x₃ → rBeta (sch (CPSCons c' (CPSVar k) (CPSVar x₃)) (CPSVar x)))))))) ⟩
  CPSLet
    (CPSVal
     (CPSFun
      (λ z →
         CPSVal
         (CPSFun
          (λ z₁ →
             CPSVal
             (CPSFun
              (λ z₂ →
                 CPSApp
                 (CPSVal
                  (CPSFun
                   (λ t'' → κ (CPSVar z) (CPSCons c' (CPSVar k) (CPSVar t'')))))
                 (CPSVal
                  (CPSAppend c₂ (CPSVar t)
                   (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))))
    (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId)
  ⟵⟨ rLet₁ (rFun (λ x → rFun (λ x₁ → rFun (λ x₂ → rLetApp)))) ⟩
  (CPSLet
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    CPSLet
                    (CPSVal
                     (CPSAppend c₂ (CPSVar t) (CPSCons c₁ (CPSVar k') (CPSVar t'))))
                    (λ t'' → κ (CPSVar v) (CPSCons c' (CPSVar k) (CPSVar t''))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id₁) CPSId))
  ∎
aux₄-s (Prompt id₁ e) κ k t c' sch = {!!}
-}


aux : {var : cpstyp → Set} {α : typ} {μα : trail} {τ₂ : typ} {μ₃ : trail}
      {μ[∙]μ₃ : trails[ ∙ ] μ₃}
      {μ[μα]μ₃ : trails[ μα ] μ₃}
      (id : is-id-trails τ₂ α μ[∙]μ₃)
      (z₁ : var (cpsT τ₂ ⇛ (cpsMs μ[μα]μ₃ ⇛ cpsT α)))
      (v : value[ var ∘ cpsT ] τ₂)
      (c : compatible (τ₂ ⇒ α , μ₃) μ₃ μ₃)
      (t' : cpsvalue[ var ] cpsMs μ[μα]μ₃) →
      cpsreduce
      (CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v))) (CPSVal t'))
      (CPSIdk id (cpsV v) (CPSCons c (CPSVar z₁) t'))

aux {μ₃ = τ ⇒ τ' , ∙} id z₁ v (refl , refl , c) t' = begin
    (CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
            (CPSVal t'))
  ⟵⟨ rApp₂ rConsid ⟩
    CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
           (CPSVal (CPSCons refl t' CPSId))
  ⟵⟨ rBeta (sApp Subst≠ (sVal (sCon SubstV≠ sVar=))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (cpsV v)))
           (CPSVal (CPSCons refl t' (CPSVar z))))))
      (CPSVal CPSId)
  ⟵⟨ rApp₁ (rBeta (sVal (sFun (λ x →
        sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ v₁ →
            CPSVal
            (CPSFun
             (λ t'' →
                CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal (CPSVar v₁)))
                (CPSVal (CPSCons refl t' (CPSVar t''))))))))
       (CPSVal (cpsV v)))
      (CPSVal CPSId)
  ⟵⟨ rApp₁ (rApp₁ rConst) ⟩
    CPSApp
      (CPSApp (CPSVal (CPSCons (refl , refl , c) (CPSVar z₁) t'))
       (CPSVal (cpsV v)))
      (CPSVal CPSId)
  ⟵⟨ rIdkt ⟩
    (CPSIdk id (cpsV v) (CPSCons (refl , refl , c) (CPSVar z₁) t'))
  ∎

------------------------------------------------------------------------------------------------------------------

correctEta : {var : cpstyp → Set} {τ₁ α β : typ} {μα μβ : trail}
             {μs : trails[ μβ ] μα} →
             {e e′ : term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β} →
             (k : cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
                  cpsterm[ var ] (cpsT α)) →
             (t : cpsvalue[ var ] (cpsM μβ)) →
             (sch : schematicV k) →
             (sch' : schematicV′ k) →
             (red : Reduce e e′) →
             cpsreduce (cpsTerm e k t) (cpsTerm e′ k t)

correctEta {μs = μs} {e′ = e′} k t sch sch' (RBeta {e₁ = e₁} {v₂ = v₂} sub) =
  begin
    cpsTerm {μs = μs} (App (Val (Fun e₁)) (Val v₂)) k t
  ⟶⟨ rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t' →
        eSubst sub (λ v → sApp (sApp (sVal sVar≠) (sVal v)) Subst≠)))))))) ⟩
    CPSApp
      (CPSApp
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                cpsTerm e′
                (λ v t'' →
                   CPSApp (CPSApp (CPSVal (CPSVar z)) (CPSVal v)) (CPSVal t''))
                (CPSVar z₁))))))
       (CPSVal
        (CPSFun
         (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t'')))))))
      (CPSVal t)
  ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ →
        kSubst e′ (λ x₂ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))) ⟩
    CPSApp
      (CPSVal
       (CPSFun
        (λ z →
           cpsTerm e′
           (λ z₁ z₂ →
              CPSApp
              (CPSApp
               (CPSVal
                (CPSFun
                 (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
               (CPSVal z₁))
              (CPSVal z₂))
           (CPSVar z))))
      (CPSVal t)
  ⟶⟨ rBeta (tSubst e′ λ t₁ v₃ → sApp Subst≠ (sVal sVar=)) ⟩
    cpsTerm e′
      (λ z₁ z₂ →
         CPSApp
         (CPSApp
          (CPSVal
           (CPSFun
            (λ v → CPSVal (CPSFun (λ t'' → k (CPSVar v) (CPSVar t''))))))
          (CPSVal z₁))
         (CPSVal z₂))
      t
  ⟶⟨ correctCont e′ _
        (λ v t' → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t' → begin
          (CPSApp
           (CPSApp
            (CPSVal
             (CPSFun
              (λ v₁ → CPSVal (CPSFun (λ t'' → k (CPSVar v₁) (CPSVar t''))))))
            (CPSVal (cpsV v)))
           (CPSVal t'))
        ⟶⟨ rApp₁ (rBeta (sVal (sFun (λ x₁ → sch v (CPSVar x₁))))) ⟩
          CPSApp (CPSVal (CPSFun (λ z → k (cpsV v) (CPSVar z)))) (CPSVal t')
        ⟶⟨ rBeta (sch' t' (cpsV v)) ⟩
          (k (cpsV v) t')
        ∎) ⟩
    cpsTerm e′ k t
  ∎

correctEta k t sch sch' (RPlus {τ₂} {μα} {n₁} {n₂}) = begin
    (CPSLet (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂)))
     (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rPlus ⟩
    CPSLet (CPSVal (CPSNum (n₁ + n₂))) (λ v → k (CPSVar v) t)
  ⟶⟨ rLet (sch (Num (n₁ + n₂)) t) ⟩
    (k (CPSNum (n₁ + n₂)) t)
  ∎

correctEta k t sch sch' (RFrame (App₁ e₂) red) =
  correctEta _ t
    (λ v₁ t₁ → kSubst e₂ (λ v₂ t₂ →
                 sApp (sApp (sApp (sVal sVar=) Subst≠) Subst≠) Subst≠))
    (λ t₁ v₁ → tSubst e₂ (λ t₂ v₂ → sApp (sApp Subst≠ Subst≠) (sVal sVar=)))
    red

correctEta k t sch sch' (RFrame (App₂ v₁) red) =
  correctEta _ t
    (λ v₁ t₁ → sApp (sApp (sApp Subst≠ (sVal sVar=)) Subst≠) Subst≠)
    (λ t₁ v₁ → sApp Subst≠ (sVal sVar=))
    red

correctEta k t sch sch' (RFrame (Plus₁ e₂) red) =
  correctEta _ t
    (λ v₁ t₁ → kSubst e₂ (λ v₂ t₂ →
                 sLet (λ n → Subst≠)
                      (λ n → sPlu (sVal sVar=) Subst≠)))
    (λ t₁ v₁ → tSubst e₂ (λ t₂ v₂ →
                 sLet (λ x₁ → sch' t₂ (CPSVar x₁)) (λ x₁ → Subst≠)))
    red

correctEta k t sch sch' (RFrame (Plus₂ v₁) red) =
  correctEta _ t
    (λ v₁ t₁ → sLet (λ n → Subst≠)
                    (λ n → sPlu Subst≠ (sVal sVar=)))
    (λ t₁ v₁ → sLet (λ n → sch' t₁ (CPSVar n))
                    (λ n → Subst≠))
    red

correctEta k t sch sch' (RFrame {e₁ = e₁} {e₂ = e₂} (Pro id) red) = begin
    (CPSLet (cpsTerm e₁ (CPSIdk id) CPSId) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ (correctEta _ CPSId
               (λ v₁ t₁ → sIdk sVar= SubstV≠)
               (λ t₁ v₁ → sIdk SubstV≠ sVar=)
               red) ⟩
    (CPSLet (cpsTerm e₂ (CPSIdk id) CPSId) (λ v → k (CPSVar v) t))
  ∎

correctEta k t sch sch' (RPrompt {v₁ = v₁}) = begin
    (CPSLet (CPSIdk refl (cpsV v₁) CPSId) (λ v → k (CPSVar v) t))
  ⟶⟨ rLet₁ rIdkid ⟩
    CPSLet (CPSVal (cpsV v₁)) (λ v → k (CPSVar v) t)
  ⟶⟨ rLetApp ⟩
    CPSApp (CPSVal (CPSFun (λ v → k (CPSVar v) t))) (CPSVal (cpsV v₁))
  ⟶⟨ rBeta (sch v₁ t) ⟩
    (k (cpsV v₁) t)
  ∎

correctEta k t sch sch'
  (RControl {μ[∙]α = μ[∙]α} {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃}
            p₁ p₂ {id₀} id c₁ refl same e) =
  begin
    (cpsTerm (Prompt id₀ (pcontext-plug p₁ (Control id c₁ refl e))) k
     t)
  ⟶⟨ rLet₁ (control-lemma p₁ p₂ c₁ refl same (Control id c₁ refl e)
                           (CPSIdk id₀) CPSId
                           (λ v t₁ → sIdk sVar= SubstV≠)
                           (λ t₁ v₂ → sIdk SubstV≠ sVar=)) ⟩
    CPSLet
      (cpsTerm {μs = μ[∙]μ₃}
       (App {μ[γ]β = μ[∙]α}
            (Val (Fun (λ x₁ → pcontext-plug p₂ (Val (Var x₁)))))
            (Control {μs₁ = μ[μα]μ₃} id c₁ refl e))
       (CPSIdk id₀) CPSId)
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
        rApp₁ (rApp₁ (rBeta (sVal (sFun (λ k → sVal (sFun (λ t →
          eSubst (subst-context p₂ (Var x₁))
                 (λ sub → sApp (sApp Subst≠ (sVal sub)) Subst≠)))))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSVal
                     (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                    (λ z₃ →
                       CPSApp
                       (CPSApp
                        (CPSVal
                         (CPSFun
                          (λ z₄ →
                             CPSVal
                             (CPSFun
                              (λ z₅ →
                                 cpsTerm (pcontext-plug p₂ (Val (Var z)))
                                 (λ v t'' →
                                    CPSApp (CPSApp (CPSVal (CPSVar z₄)) (CPSVal v)) (CPSVal t''))
                                 (CPSVar z₅))))))
                        (CPSVal
                         (CPSFun
                          (λ v →
                             CPSVal (CPSFun (λ t'' → CPSIdk id₀ (CPSVar v) (CPSVar t'')))))))
                       (CPSVal (CPSVar z₃))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
        rApp₁ (rBeta (sVal (sFun (λ x₅ →
          kSubst (pcontext-plug p₂ (Val (Var x₁)))
            (λ x₆ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSVal
                     (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                    (λ z₃ →
                       CPSApp
                       (CPSVal
                        (CPSFun
                         (λ z₄ →
                            cpsTerm (pcontext-plug p₂ (Val (Var z)))
                            (λ z₅ z₆ →
                               CPSApp
                               (CPSApp
                                (CPSVal
                                 (CPSFun
                                  (λ v →
                                     CPSVal (CPSFun (λ t'' → CPSIdk id₀ (CPSVar v) (CPSVar t''))))))
                                (CPSVal z₅))
                               (CPSVal z₆))
                            (CPSVar z₄))))
                       (CPSVal (CPSVar z₃))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
       rBeta (tSubst (pcontext-plug p₂ (Val (Var x₁)))
                     (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSVal
                     (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ z₅ z₆ →
                          CPSApp
                          (CPSApp
                           (CPSVal
                            (CPSFun
                             (λ v →
                                CPSVal (CPSFun (λ t'' → CPSIdk id₀ (CPSVar v) (CPSVar t''))))))
                           (CPSVal z₅))
                          (CPSVal z₆))
                       (CPSVar z₃)))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁))) _
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ →
          rApp₁ (rBeta (sVal (sFun (λ x₅ → sIdk sVar= SubstV≠))))))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSVal
                     (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' →
                          CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id₀ v (CPSVar t'''))))
                          (CPSVal t''))
                       (CPSVar z₃)))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLet₂ (λ x₄ →
      correctCont (pcontext-plug p₂ (Val (Var x₁))) _
        {k₂ = λ v t'' → CPSIdk id₀ v t''}
        (λ v t₁ → sApp (sVal (sFun (λ x₅ → sIdk sVar= SubstV≠))) Subst≠)
        (λ v t₁ → rBeta (sIdk SubstV≠ sVar=)))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet
                    (CPSVal
                     (CPSAppend refl CPSId (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ v t'') (CPSVar z₃)))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ →
        rLet₁ rApdid))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSLet (CPSVal (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))
                    (λ z₃ →
                       cpsTerm (pcontext-plug p₂ (Val (Var z)))
                       (λ v t'' → CPSIdk id₀ v t'') (CPSVar z₃)))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ → rLetApp))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    CPSApp
                    (CPSVal
                     (CPSFun
                      (λ z₃ →
                         cpsTerm (pcontext-plug p₂ (Val (Var z)))
                         (λ v t'' → CPSIdk id₀ v t'') (CPSVar z₃))))
                    (CPSVal (CPSCons c₁ (CPSVar z₁) (CPSVar z₂))))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ →
        rBeta (tSubst (pcontext-plug p₂ (Val (Var x₁)))
                      (λ t₁ v₂ → sIdk SubstV≠ sVar=))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z))) (CPSIdk id₀)
                    (CPSCons c₁ (CPSVar z₁) (CPSVar z₂)))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
    ⟶⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ →
           aux₄-s (pcontext-plug p₂ (Val (Var x₁))) (CPSIdk id₀) x₂ x₃
                  (extend-compatible' c₁ (proj₂ (diff-compatible μ[μα]μ₃)))
                  (λ t₁ v₂ → sIdk SubstV≠ sVar=)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ v t' →
                       CPSIdk id₀ v
                       (CPSCons (extend-compatible' c₁ (proj₂ (diff-compatible μ[μα]μ₃)))
                        (CPSVar z₁) t'))
                    (CPSVar z₂))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₁ (rFun (λ x₁ → rFun (λ x₂ → rFun (λ x₃ →
        correctCont (pcontext-plug p₂ (Val (Var x₁))) _
          {k₂ = λ v t'' → CPSIdk id₀ v
            (CPSCons (extend-compatible' c₁
                       (proj₂ (diff-compatible μ[μα]μ₃))) (CPSVar x₂) t'')}
          (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
          (λ v t₁ → aux {μ[∙]μ₃ = μ[∙]μ₃} {μ[μα]μ₃ = μ[μα]μ₃}
            id₀ x₂ v (extend-compatible' c₁
                       (proj₂ (diff-compatible μ[μα]μ₃))) t₁)))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ z →
            CPSVal
            (CPSFun
             (λ z₁ →
                CPSVal
                (CPSFun
                 (λ z₂ →
                    cpsTerm (pcontext-plug p₂ (Val (Var z)))
                    (λ z₃ z₄ →
                       CPSApp (CPSApp (CPSVal (CPSVar z₁)) (CPSVal z₃)) (CPSVal z₄))
                    (CPSVar z₂))))))))
       (λ x' → cpsTerm (e x') (CPSIdk id) CPSId))
      (λ v → k (CPSVar v) t)
  ≡⟨ refl ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z → cpsTerm (e z) (λ v t'' → CPSIdk id v t'') CPSId))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₁ →
      correctCont (e x₁) _
        {k₂ = λ v t'' → CPSIdk id v t''} (λ v t₁ →
        sApp (sVal (sFun (λ x₂ → sIdk sVar= SubstV≠))) Subst≠)
        (λ v t₁ → rBeta (sIdk SubstV≠ sVar=)))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z)
          (λ v t'' →
             CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id v (CPSVar t'''))))
             (CPSVal t''))
          CPSId))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₁ →
      correctCont (e x₁) _
        {k₂ =
         λ v t'' →
           CPSApp (CPSVal (CPSFun (λ t''' → CPSIdk id v (CPSVar t'''))))
           (CPSVal t'')}
        (λ v t₁ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)
        (λ v t₁ → rApp₁ (rBeta (sVal (sFun (λ x₂ → sIdk sVar= SubstV≠))))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ z →
          cpsTerm (e z)
          (λ z₁ z₂ →
             CPSApp
             (CPSApp
              (CPSVal
               (CPSFun
                (λ v →
                   CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t''))))))
              (CPSVal z₁))
             (CPSVal z₂))
          CPSId))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rLet₂ (λ x₁ →
        rBeta (tSubst (e x₁) (λ t₁ v₂ → sApp Subst≠ (sVal sVar=))))) ⟩
    CPSLet
      (CPSLet
       (CPSVal
        (CPSFun
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (pcontext-plug p₂ (Val (Var x)))
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))))
       (λ x →
          CPSApp
          (CPSVal
           (CPSFun
            (λ z₁ →
               cpsTerm (e x)
               (λ z₂ z₃ →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v →
                        CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t''))))))
                   (CPSVal z₂))
                  (CPSVal z₃))
               (CPSVar z₁))))
          (CPSVal CPSId)))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ rLet₃ ⟩
    CPSLet
      (CPSApp
       (CPSLet
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (λ z →
           CPSVal
           (CPSFun
            (λ z₁ →
               cpsTerm (e z)
               (λ z₂ z₃ →
                  CPSApp
                  (CPSApp
                   (CPSVal
                    (CPSFun
                     (λ v →
                        CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t''))))))
                   (CPSVal z₂))
                  (CPSVal z₃))
               (CPSVar z₁)))))
       (CPSVal CPSId))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ (rLet₂ (λ x₁ → rBeta (sVal (sFun (λ x₂ →
        kSubst (e x₁)
          (λ x₃ t₁ → sApp (sApp (sVal sVar=) Subst≠) Subst≠))))))) ⟩
    CPSLet
      (CPSApp
       (CPSLet
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (λ x →
           CPSApp
           (CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (e x)
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t'))))))
           (CPSVal
            (CPSFun
             (λ v →
                CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t''))))))))
       (CPSVal CPSId))
      (λ v → k (CPSVar v) t)
  ⟵⟨ rLet₁ (rApp₁ rLet₃) ⟩
    CPSLet
      (CPSApp
       (CPSApp
        (CPSLet
         (CPSVal
          (CPSFun
           (λ x →
              CPSVal
              (CPSFun
               (λ k' →
                  CPSVal
                  (CPSFun
                   (λ t' →
                      cpsTerm (pcontext-plug p₂ (Val (Var x)))
                      (λ v t'' →
                         CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                      (CPSVar t'))))))))
         (λ x →
            CPSVal
            (CPSFun
             (λ k' →
                CPSVal
                (CPSFun
                 (λ t' →
                    cpsTerm (e x)
                    (λ v t'' →
                       CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v)) (CPSVal t''))
                    (CPSVar t')))))))
        (CPSVal
         (CPSFun
          (λ v →
             CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t'')))))))
       (CPSVal CPSId))
      (λ v → k (CPSVar v) t)
  ⟶⟨ rLet₁ (rApp₁ (rApp₁ rLetApp)) ⟩
    (CPSLet
     (CPSApp
      (CPSApp
       (CPSApp
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (e x)
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k'))
                                       (CPSVal v)) (CPSVal t''))
                     (CPSVar t'))))))))
        (CPSVal
         (CPSFun
          (λ x →
             CPSVal
             (CPSFun
              (λ k' →
                 CPSVal
                 (CPSFun
                  (λ t' →
                     cpsTerm (pcontext-plug p₂ (Val (Var x)))
                     (λ v t'' →
                        CPSApp (CPSApp (CPSVal (CPSVar k'))
                                       (CPSVal v)) (CPSVal t''))
                     (CPSVar t')))))))))
       (CPSVal
        (CPSFun
         (λ v →
            CPSVal (CPSFun (λ t'' → CPSIdk id (CPSVar v) (CPSVar t'')))))))
      (CPSVal CPSId))
     (λ v → k (CPSVar v) t))
  ∎
