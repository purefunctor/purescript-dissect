let conf = ./spago.dhall

in      conf
    //  { dependencies =
              conf.dependencies
            # [ "console", "effect", "fixed-points", "lists", "psci-support" ]
        , sources = conf.sources # [ "test/**/*.purs" ]
        }
