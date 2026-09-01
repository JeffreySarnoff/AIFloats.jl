# shared test helpers — included once per test file that needs them (guarded
# by isdefined, since every test file is included into the same Main)
allcodes(F) = [fromcode(F, c) for c in 0:(2^Int(BitwidthOf(F)) - 1)]
subcodes(F, n) = (xs = allcodes(F); step = max(1, cld(length(xs), n)); unique(vcat(xs[1:step:end], xs[end])))
