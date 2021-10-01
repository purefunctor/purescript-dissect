{ name = "dissect"
, dependencies =
  [ "bifunctors"
  , "either"
  , "fixed-points"
  , "functors"
  , "partial"
  , "prelude"
  , "tailrec"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/PureFunctor/purescript-dissect.git"
}
