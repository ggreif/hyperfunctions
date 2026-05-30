{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Constructor.Syntax
  ( Lang (..)
  , HasAnn (..)
  , Name
  ) where

import Constructor.Path (Path)
import Constructor.Sort (Sort (..))
import Data.Functor.Const (Const (..))
import Data.Kind (Type)
import Data.Text (Text)

-- | Identifiers (declared names, variable references).
type Name = Text

-- | Finally-tagless algebra for the constructor language, HKT'd in the
--   annotation kind @a :: Sort -> Type@ (Trees-that-Grow style).  Each
--   method takes a per-sort annotation slot; instances are usually
--   polymorphic in @a@ and just thread it through.  See 'HasAnn' for
--   the convention by which producers (e.g. the parser) obtain
--   annotation values without committing to a particular phase.
--
--   'forallLv' and 'starVar' carry universe polymorphism.  They have
--   error defaults so carriers that don't (yet) support polymorphism
--   can omit them — those carriers crash if asked to interpret a
--   polymorphic input, which is honest about what they support.
class Lang (r :: (Sort -> Type) -> Sort -> Type) where
  prog     :: a 'SProg -> [r a 'SDecl] -> r a 'SProg
  -- | Data declaration.  The first 'Path' is the declaration's
  --   def-path — supplied by the parser so carriers can construct
  --   the data's own @TyConV name declPath@ view (e.g.\ for kind
  --   coherence checking).
  --
  --   The parameter list is @[(Name, Maybe (r a \'SExpr))]@ — each
  --   parameter is a name plus an optional kind annotation (the
  --   @K@ in @data Foo (a : K) : *0 ...@).  When the annotation is
  --   absent (bare @data Foo a@ syntax), the carrier is free to
  --   pick a default kind (today: @*0@ everywhere).  The kind
  --   annotation is parsed against the binders OUTSIDE the data
  --   body — each param's kind cannot reference earlier params
  --   (so @data Foo (a : Nat) (b : a)@ is a future extension, not
  --   today's behaviour).  The annotation is currently consumed
  --   only by carriers that want to set the param's level
  --   appropriately; carriers can ignore it (destructure as @(n,
  --   _)@) and behave as if no annotation was present.
  dataDecl
    :: a 'SDecl
    -> Path
    -> Name
    -> [(Name, Maybe (r a 'SExpr))]
    -> r a 'SExpr
    -> [r a 'SDecl]
    -> r a 'SDecl
  ctorDecl :: a 'SDecl -> Name -> r a 'SExpr -> r a 'SDecl
  var      :: a 'SExpr -> Name -> r a 'SExpr
  star     :: a 'SExpr -> Word -> r a 'SExpr
  arr      :: a 'SExpr -> r a 'SExpr -> r a 'SExpr -> r a 'SExpr
  -- | Type-level application: @f x@.  Left-associative juxtaposition
  --   at the surface; @f x y@ parses to @app (app f x) y@ — every
  --   nested @App@ within a single source-level application shares
  --   the same 'Path', namely the path of the application as a
  --   whole.  Carriers performing parametric instantiation use that
  --   path as the use-site address for fresh metavariables; carriers
  --   that don't may ignore it.
  app      :: a 'SExpr -> Path -> r a 'SExpr -> r a 'SExpr -> r a 'SExpr
  app = error "Lang.app: application not supported by this carrier"

  -- | Reference to a type parameter introduced by a 'data' declaration.
  --   Distinct from 'var' because the parser knows the resolved
  --   binder path: the @Name@ is the surface name (for display); the
  --   @Path@ is the parameter's def-position.  Same shape as
  --   'starVar' for the level layer.
  tyParamRef :: a 'SExpr -> Name -> Path -> r a 'SExpr
  tyParamRef = error "Lang.tyParamRef: type-parameter resolution not supported by this carrier"

  -- | Reference to a type constructor introduced by a 'data'
  --   declaration.  Distinct from 'var' for the same reason
  --   'tyParamRef' is: the parser has resolved the surface name to
  --   the @Path@ of the introducing @data@ declaration.  For nullary
  --   tycons the use-path collapses to the def-path (use-paths
  --   identified with def-path by transitivity — \(x^0 = 1\)); for
  --   higher-kinded tycons the use-path will additionally address
  --   instantiation freshness (a later commit).
  tyConRef :: a 'SExpr -> Name -> Path -> r a 'SExpr
  tyConRef = error "Lang.tyConRef: type-constructor resolution not supported by this carrier"

  -- | Level-binder introduction: @∀l. body@.  The @Name@ is the
  --   binder's surface name (for display); the @Path@ is its
  --   syntactic identity (replaces the counter-based fresh id).
  --   Inside @body@ the parser parses references to that name (in
  --   universe positions) via 'starVar' with the same 'Path'.
  forallLv :: a 'SExpr -> Name -> Path -> r a 'SExpr -> r a 'SExpr
  forallLv = error "Lang.forallLv: level polymorphism not supported by this carrier"

  -- | Variable-shifted universe: @*(l + n)@.  The @Name@ is the
  --   binder's surface name; the @Path@ is the binder's identity
  --   (resolved by the parser via name lookup); the @Word@ is the
  --   offset.  Bare @*l@ parses to @starVar ann l p 0@.
  starVar  :: a 'SExpr -> Name -> Path -> Word -> r a 'SExpr
  starVar  = error "Lang.starVar: level polymorphism not supported by this carrier"

  -- | Existential type-variable binder: @∃ m. T@.  Introduces a
  --   fresh type variable @m@ at the ctor's scope; @T@ is parsed
  --   with @m@ in 'tyBinders'.  The 'Path' is the binder's identity
  --   (replaces a per-parse counter); 'tyParamRef' inside @T@ with
  --   the same 'Path' refers to this existential.
  --
  --   Semantically: at the ctor type, the existential is hidden
  --   (only the ctor knows what @m@ is); when pattern-matching
  --   that ctor, @m@ becomes a fresh skolem in the match arm.
  --   The gabor/gadt invariant — refinements must never equate
  --   to existentials — is the operational consequence at
  --   pattern-match time.  For step 3c-a the binder is parsed
  --   and threaded through Lang; the refinement-on-match
  --   semantics is a later step.
  --
  --   Default for carriers that don't yet handle existentials:
  --   pass through the body (the existential becomes a regular
  --   tyVar at the level layer, kind defaults to @*0@).
  existsTy :: a 'SExpr -> Name -> Path -> r a 'SExpr -> r a 'SExpr
  existsTy = error "Lang.existsTy: existential type binders not supported by this carrier"

-- | Annotation provider in an applicative monad @m@.  The parser is
--   written generically against 'HasAnn', so it can produce trees at
--   any annotation regime without further refactoring.
class Applicative m => HasAnn (a :: Sort -> Type) (m :: Type -> Type) where
  freshExprAnn :: m (a 'SExpr)
  freshDeclAnn :: m (a 'SDecl)
  freshProgAnn :: m (a 'SProg)

-- | Trivial annotations: every slot is @Const ()@.  Works for any
--   applicative monad — the raw-parsing default.
instance Applicative m => HasAnn (Const ()) m where
  freshExprAnn = pure (Const ())
  freshDeclAnn = pure (Const ())
  freshProgAnn = pure (Const ())
