{ name = "dissect"
, dependencies =
  [ "aff"
  , "arrays"
  , "bifunctors"
  , "effect"
  , "foreign-object"
  , "functors"
  , "newtype"
  , "partial"
  , "prelude"
  , "spec"
  , "tailrec"
  , "type-equality"
  , "typelevel-prelude"
  , "unsafe-coerce"
  , "variant"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/PureFunctor/purescript-dissect.git"
}
