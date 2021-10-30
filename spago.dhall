{ name = "dissect"
, dependencies =
  [ "bifunctors"
  , "functors"
  , "partial"
  , "prelude"
  , "tailrec"
  , "typelevel-prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/PureFunctor/purescript-dissect.git"
}
