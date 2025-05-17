binary5p3es_nonneg = [0.0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1.0,
               1.25, 1.5, 1.75, 2.0, 2.5, 3.0,
               Inf]
binary5p3es_neg = -1.0 .* binary5p3es_nonneg[2:end]
binary5p3es = append!(binary5p3es_nonneg, [NaN], binary5p3es_neg)
binary5p3es_nprenormalmagitudes = 4
binary5p3es_nsubnormalmagitudes = binary5p3es_nprenormalmagitudes - 1
binary5p3es_minexp = -1
binary5p3es_maxexp = 1
binary5p3es_exprun = 4

# divrem(32,4) = (8, 0). divrem(16, 4) = (4, 0)
# first is for prenormal mags, leaving 3 normal mag exponent runs of 4
#
# 