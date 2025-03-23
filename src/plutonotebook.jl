### A Pluto.jl notebook ###
# v0.20.5

using Markdown
using InteractiveUtils

# ╔═╡ a3525297-6b2d-400d-818c-2adfe09158de
abstract type AbstractFloatML{Bits, SigBits} <: AbstractFloat end

# ╔═╡ ffea6a2b-59cb-4f74-9c7f-aa2e70e5b4b8
struct FoundFloat{Bits, SigBits} <: AbstractFloatML{Bits, SigBits}
    rationals::Vector{Float32}    # rationals given as nearest Flaat32
	offsets::Vector{UInt8}        # value encodings .. indices given as 0-based
end

# ╔═╡ 96d5d993-511d-47d2-8311-a9f616debf43
nbits(T::Type{FoundFloat{Bits, SigBits}}) where {Bits, SigBits} = Bits

# ╔═╡ bf029e1c-5988-406a-9920-7b769cd7eb71
nsigbits(T::Type{FoundFloat{Bits, SigBits}}) where{Bits, SigBits} = SigBits

# ╔═╡ 9bde1711-bb18-415c-aebd-ab5a3c7cbd77
nfracbits(::Type{FoundFloat{Bits, SigBits}}) where {Bits, SigBits} =
	nsigbits - 1

# ╔═╡ 36521b16-d5d8-44d6-a57f-5e0a5647fef6
nexpbits(::Type{FoundFloat{Bits, SigBits}}) where {Bits, SigBits} =
	Bits - SigBits

# ╔═╡ 2d84ee7f-36b9-4a2b-a2fb-4a3b7d00ff4e
# how many exponent values?
nexpvalues(::Type{FoundFloat{Bits, SigBits}}) where {Bits, SigBits} =
	2^nexpbits(T)

# ╔═╡ d75ce239-9192-4e7d-b7ed-7a1d2e677e8f
# how many subnormal magnitudes?
nsubnormal_mags(::Type{FoundFloat{Bits, SigBits}}) where {Bits, SigBits} =
	2^SigBits - 1

# ╔═╡ 8e182f3a-2343-4284-8dde-74dd749d6443
# how many normal magnitudes?
# nnormal_mags(::Type{FoundFloat{Bits, SigBits}}) where {Bits, SigBits} =
#	2^Bits - nsubnormal_mags(

# ╔═╡ Cell order:
# ╠═a3525297-6b2d-400d-818c-2adfe09158de
# ╠═ffea6a2b-59cb-4f74-9c7f-aa2e70e5b4b8
# ╠═96d5d993-511d-47d2-8311-a9f616debf43
# ╠═bf029e1c-5988-406a-9920-7b769cd7eb71
# ╠═9bde1711-bb18-415c-aebd-ab5a3c7cbd77
# ╠═36521b16-d5d8-44d6-a57f-5e0a5647fef6
# ╠═2d84ee7f-36b9-4a2b-a2fb-4a3b7d00ff4e
# ╠═d75ce239-9192-4e7d-b7ed-7a1d2e677e8f
# ╠═8e182f3a-2343-4284-8dde-74dd749d6443