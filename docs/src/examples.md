# Examples

This section provides comprehensive examples demonstrating AIFloats.jl in realistic machine learning scenarios, showcasing both basic usage patterns and advanced optimization techniques.

## Neural Network Quantization

### Weight Quantization Pipeline

```julia
using AIFloats
using Random, Statistics

# Simulate a small neural network layer
Random.seed!(42)
weights_fp32 = randn(Float32, 8, 8) * 0.3  # Layer weights
biases_fp32 = randn(Float32, 8) * 0.1      # Bias terms

# Choose quantization formats based on value distributions
weight_format = AIFloat(6, 3, :signed, :finite)    # 6-bit weights: [-1.75, +1.75]
bias_format = AIFloat(8, 4, :signed, :finite)      # 8-bit biases: higher precision

function quantize_tensor(values::Array{T}, format::AbstractAIFloat) where T
    quantized = similar(values, eltype(floats(format)))
    
    for i in eachindex(values)
        # Find nearest representable value
        distances = abs.(floats(format) .- values[i])
        closest_idx = argmin(distances)
        quantized[i] = floats(format)[closest_idx]
    end
    
    return quantized
end

# Perform quantization
weights_quantized = quantize_tensor(weights_fp32, weight_format)
biases_quantized = quantize_tensor(biases_fp32, bias_format)

# Analyze quantization impact
weight_mse = mean((weights_fp32 .- weights_quantized).^2)
bias_mse = mean((biases_fp32 .- biases_quantized).^2)

println("Weight quantization MSE: $(weight_mse)")
println("Bias quantization MSE: $(bias_mse)")
println("Compression ratio: $(sizeof(weights_fp32) / sizeof(Int8.(codes(weight_format)[1:64])))")
```

### Activation Function Tables

Generate optimized lookup tables for common activation functions:

```julia
# Create lookup tables for small formats
activation_format = AIFloat(5, 3, :signed, :finite)
input_vals = floats(activation_format)

# ReLU lookup table
relu_table = max.(0.0, input_vals)

# Sigmoid approximation lookup table  
sigmoid_table = 1.0 ./ (1.0 .+ exp.(-input_vals))

# Tanh lookup table
tanh_table = tanh.(input_vals)

# Demonstrate table-based computation
function table_relu(code::UInt8, format::AbstractAIFloat, table::Vector)
    return table[code + 1]  # +1 for Julia indexing
end

# Performance comparison
input_code = 0x05
table_result = table_relu(input_code, activation_format, relu_table)
direct_result = max(0.0, floats(activation_format)[input_code + 1])

println("Table lookup: $(table_result)")
println("Direct computation: $(direct_result)")
println("Results match: $(table_result == direct_result)")
```

## Gradient Compression

### Stochastic Quantization for Gradients

```julia
using AIFloats

# Simulate gradient tensor
gradient_fp32 = randn(Float32, 100) * 0.01  # Small gradients typical in training

# Ultra-low precision for gradient compression
grad_format = AIFloat(4, 2, :signed, :finite)  # 4-bit gradients

function stochastic_quantize(value::T, format::AbstractAIFloat) where T
    values = floats(format)
    
    # Find bracketing values
    finite_vals = values[.!isnan.(values) .&& .!isinf.(values)]
    
    if value <= minimum(finite_vals)
        return minimum(finite_vals)
    elseif value >= maximum(finite_vals)
        return maximum(finite_vals)
    end
    
    # Find upper and lower bounds
    upper_idx = findfirst(v -> v >= value, finite_vals)
    lower_idx = upper_idx - 1
    
    upper_val = finite_vals[upper_idx]
    lower_val = finite_vals[lower_idx]
    
    # Stochastic rounding based on distance
    distance_to_lower = abs(value - lower_val)
    distance_to_upper = abs(value - upper_val)
    total_distance = distance_to_lower + distance_to_upper
    
    prob_upper = distance_to_lower / total_distance
    
    return rand() < prob_upper ? upper_val : lower_val
end

# Apply stochastic quantization
gradients_quantized = [stochastic_quantize(g, grad_format) for g in gradient_fp32]

# Analyze compression and error
original_entropy = -sum(p * log2(p) for p in [count(==(v), gradient_fp32)/length(gradient_fp32) for v in unique(gradient_fp32)] if p > 0)
compressed_entropy = -sum(p * log2(p) for p in [count(==(v), gradients_quantized)/length(gradients_quantized) for v in unique(gradients_quantized)] if p > 0)

println("Original gradient entropy: $(original_entropy) bits")
println("Compressed gradient entropy: $(compressed_entropy) bits")
println("Compression ratio: $(32 / 4)x")  # Float32 to 4-bit
```

## Attention Mechanism Optimization

### Multi-Head Attention with Mixed Precision

```julia
using AIFloats
using LinearAlgebra

# Simulate attention computation with different precisions
seq_length, d_model, n_heads = 64, 256, 8
d_k = d_model ÷ n_heads

# Format selection for different components
query_format = AIFloat(8, 4, :signed, :finite)     # 8-bit queries
key_format = AIFloat(8, 4, :signed, :finite)       # 8-bit keys  
value_format = AIFloat(6, 3, :signed, :finite)     # 6-bit values
attention_format = AIFloat(6, 3, :unsigned, :finite) # 6-bit attention weights

# Generate synthetic attention inputs
Q_fp32 = randn(Float32, seq_length, d_k) * 0.1
K_fp32 = randn(Float32, seq_length, d_k) * 0.1  
V_fp32 = randn(Float32, seq_length, d_k) * 0.5

# Quantize inputs
Q_quantized = quantize_tensor(Q_fp32, query_format)
K_quantized = quantize_tensor(K_fp32, key_format)
V_quantized = quantize_tensor(V_fp32, value_format)

# Attention computation in mixed precision
function mixed_precision_attention(Q, K, V, attn_format)
    # Compute attention scores (Q * K^T)
    scores = Q * K'
    
    # Apply scaling
    scores = scores ./ sqrt(size(K, 2))