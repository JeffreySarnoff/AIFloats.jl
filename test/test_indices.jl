using Test
using AIFloats
using AIFloats: UnsignedFiniteFloat, SignedFiniteFloat,
                  UnsignedExtendedFloat, SignedExtendedFloat,
                  offset_to_index, index_to_offset, index_to_code,
                  idxone, idxnan, idxinf, idxneginf, idxnegone,
                  ofsone, ofsnan, ofsinf, ofsneginf,
                  is_idxnan, is_ofsnan,
                  nValues, floats,
                  index1, value_to_index, index_to_value,
                  value_to_indices, value_to_indexgte
using Static

@testset "Indices Tests" begin
    @testset "Offset/Index Conversion" begin
        # Test basic conversions
        @test offset_to_index(0) == 1
        @test offset_to_index(5) == 6
        @test offset_to_index(255) == 256
        
        @test index_to_offset(1) == 0
        @test index_to_offset(6) == 5
        @test index_to_offset(256) == 255
        
        # Test with static integers
        @test offset_to_index(static(10)) == 11
        @test index_to_offset(static(11)) == 10
        
        # Test type-specific conversions
        @test offset_to_index(UInt16, 100) == UInt16(101)
        @test index_to_offset(UInt8, 50) == UInt8(49)
    end
    
    @testset "Index/Code Conversion" begin
        # Test 8-bit encoding
        @test index_to_code(8, 1) == UInt8(0)
        @test index_to_code(8, 256) == UInt8(255)
        
        # Test 16-bit encoding  
        @test index_to_code(9, 1) == UInt16(0)
        @test index_to_code(9, 512) == UInt16(511)
        
        # Test bit width determines type
        @test index_to_code(8, 100) isa UInt8
        @test index_to_code(9, 100) isa UInt16
    end
    
    @testset "Special Index Functions" begin
        # Create test types
        uf = UnsignedFiniteFloat(6, 3)
        sf = SignedFiniteFloat(6, 3)
        
        # Test index1 function
        @test index1(typeof(uf)) isa Integer
        @test index1(typeof(sf)) isa Integer
        @test index1(uf) == index1(typeof(uf))
        @test index1(sf) == index1(typeof(sf))
        
        # For unsigned: should be roughly half + 1
        @test index1(typeof(uf)) == (nValues(typeof(uf)) >> 1) + 1
        
        # For signed: should be roughly quarter + 1  
        @test index1(typeof(sf)) == (nValues(typeof(sf)) >> 2) + 1
    end
    
    @testset "Value/Index Mapping" begin
        uf = UnsignedFiniteFloat(6, 3)
        values = floats(uf)
        
        # Test value_to_index
        for i in [1, 5, 10, length(values)]
            if i <= length(values)
                val = values[i]
                found_idx = value_to_index(uf, val)
                if !isnan(val)
                    @test found_idx == i
                end
            end
        end
        
        # Test index_to_value
        for i in 1:min(10, length(values))
            val = index_to_value(uf, i)
            @test val == values[i]
        end
        
        # Test out-of-bounds
        @test isnan(index_to_value(uf, 0))
        @test isnan(index_to_value(uf, length(values) + 1))
    end
    
    @testset "Special Value Indices" begin
        # Test with unsigned finite
        uf = UnsignedFiniteFloat(6, 3)
        
        # Test NaN index
        nan_idx = idxnan(typeof(uf))
        @test nan_idx isa Integer
        @test nan_idx > 0
        @test nan_idx <= nValues(typeof(uf))
        
        # Test one index
        one_idx = idxone(typeof(uf))
        @test one_idx isa Integer
        @test one_idx > 0
        @test one_idx <= nValues(typeof(uf))
        
        # Test with unsigned extended (has infinity)
        ue = UnsignedExtendedFloat(6, 3)
        inf_idx = idxinf(typeof(ue))
        @test inf_idx isa Integer
        @test inf_idx > 0
        
        # Test with signed types
        sf = SignedFiniteFloat(6, 3)
        
        nan_idx_s = idxnan(typeof(sf))
        one_idx_s = idxone(typeof(sf))
        negone_idx_s = idxnegone(typeof(sf))
        
        @test nan_idx_s isa Integer
        @test one_idx_s isa Integer  
        @test negone_idx_s isa Integer
        @test one_idx_s != negone_idx_s
    end
    
    @testset "Offset Functions" begin
        uf = UnsignedFiniteFloat(6, 3)
        
        # Test offset functions
        one_ofs = ofsone(typeof(uf))
        nan_ofs = ofsnan(typeof(uf))
        
        @test one_ofs == index_to_offset(idxone(typeof(uf)))
        @test nan_ofs == index_to_offset(idxnan(typeof(uf)))
        
        # Test with extended types
        ue = UnsignedExtendedFloat(6, 3)
        inf_ofs = ofsinf(typeof(ue))
        @test inf_ofs == index_to_offset(idxinf(typeof(ue)))
        
        # Test with signed extended
        se = SignedExtendedFloat(6, 3)
        inf_ofs_s = ofsinf(typeof(se))
        neginf_ofs_s = ofsneginf(typeof(se))
        @test inf_ofs_s != neginf_ofs_s
    end
    
    @testset "NaN Detection" begin
        uf = UnsignedFiniteFloat(6, 3)
        
        # Test index-based NaN detection
        nanidx = idxnan(uf)
        @test is_idxnan(uf, nanidx)
        @test !is_idxnan(uf, nanidx - 0x01)  # Adjacent index should not be NaN
        
        # Test offset-based NaN detection  
        nanofs = ofsnan(typeof(uf))
        @test is_ofsnan(uf, nanofs)
        @test !is_ofsnan(uf, nanofs - 0x01)
        
        # Test value-based NaN detection
        @test Base.isnan(uf, NaN32)
        @test !Base.isnan(uf, 1.0f0)
    end
    
    @testset "Index Bounds and Validation" begin
        uf = UnsignedFiniteFloat(8, 4)
        n_vals = nValues(typeof(uf))
        
        # Test that special indices are within bounds
        @test 1 <= idxone(typeof(uf)) <= n_vals
        @test 1 <= idxnan(typeof(uf)) <= n_vals
        
        # Test with extended types
        ue = UnsignedExtendedFloat(8, 4)
        @test 1 <= idxinf(typeof(ue)) <= n_vals
        
        # Test signed types
        sf = SignedFiniteFloat(8, 4)
        @test 1 <= idxone(typeof(sf)) <= n_vals
        @test 1 <= idxnegone(typeof(sf)) <= n_vals
        @test 1 <= idxnan(typeof(sf)) <= n_vals
        
        se = SignedExtendedFloat(8, 4)
        @test 1 <= idxinf(typeof(se)) <= n_vals
        @test 1 <= idxneginf(typeof(se)) <= n_vals
    end
    
    @testset "Value/Index Consistency" begin
        uf = UnsignedFiniteFloat(6, 3)
        values = floats(uf)
        
        # Test round-trip conversion for valid indices
        for i in 1:min(10, length(values))
            val = index_to_value(uf, i)
            if !isnan(val)
                found_idx = value_to_index(uf, val)
                @test found_idx == i
            end
        end
        
        # Test that value_to_index returns nothing for non-existent values
        non_existent = 12345.6789
        @test value_to_index(uf, non_existent) === nothing
    end
    
    @testset "Index Functions with Instances" begin
        # Test that index functions work with both types and instances
        uf_type = UnsignedFiniteFloat{6, 3}
        uf_instance = UnsignedFiniteFloat(6, 3)
        
        @test idxone(uf_type) == idxone(uf_instance)
        @test idxnan(uf_type) == idxnan(uf_instance)
        @test ofsone(uf_type) == ofsone(uf_instance)
        @test ofsnan(uf_type) == ofsnan(uf_instance)
    end
    
    @testset "Edge Cases and Error Handling" begin
        uf = UnsignedFiniteFloat(6, 3)
        
        # Test with extreme indices
        @test isnan(index_to_value(uf, -1))
        @test isnan(index_to_value(uf, 0))
        @test isnan(index_to_value(uf, 1000))
          
        # Test value_to_index with special values
        @test value_to_index(uf, Inf) === nothing
        @test value_to_index(uf, -Inf) === nothing
        # NaN case depends on implementation
        
        # Test conversion edge cases
        @test offset_to_index(typemax(UInt16)-1) == typemax(UInt16)
        # Note: This might overflow, which is expected behavior
    end
    
    @testset "Type Consistency" begin
        # Test that index functions return consistent types
        uf = UnsignedFiniteFloat(8, 4)
        
        @test idxone(typeof(uf)) isa Integer
        @test idxnan(typeof(uf)) isa Integer
        @test ofsone(typeof(uf)) isa Integer
        @test ofsnan(typeof(uf)) isa Integer
        
        # Test that conversions preserve appropriate types
        @test offset_to_index(UInt8(100)) isa UInt16
        @test index_to_offset(UInt16(100)) isa UInt16
        @test index_to_code(8, 100) isa UInt8
        @test index_to_code(16, 100) isa UInt16
    end
    
    @testset "Functional Relationships" begin
        # Test mathematical relationships between conversion functions
        for offset in [0, 10, 50, 255]
            index = offset_to_index(offset)
            back_to_offset = index_to_offset(index)
            @test back_to_offset == offset
        end
        
        for index in [1, 11, 51, 256]
            offset = index_to_offset(index)
            back_to_index = offset_to_index(offset)
            @test back_to_index == index
        end
    end
    
    @testset "Static vs Dynamic Behavior" begin
        # Test that static and dynamic versions give same results
        test_vals = [0, 5, 10, 255]
        
        for val in test_vals
            static_result = offset_to_index(static(val))
            dynamic_result = offset_to_index(val)
            @test static_result == dynamic_result
            
            static_result_back = index_to_offset(static(val + 1))
            dynamic_result_back = index_to_offset(val + 1)
            @test static_result_back == dynamic_result_back
        end
    end
    
    @testset "Signed vs Unsigned Index Patterns" begin
        # Compare index patterns between signed and unsigned types
        uf = UnsignedFiniteFloat(8, 4)
        sf = SignedFiniteFloat(8, 4)
        
        # Both should have valid one indices
        uf_one_idx = idxone(typeof(uf))
        sf_one_idx = idxone(typeof(sf))
        
        @test uf_one_idx > 0
        @test sf_one_idx > 0
        @test uf_one_idx != sf_one_idx  # Should be different
        
        # Both should have valid NaN indices
        uf_nan_idx = idxnan(typeof(uf))
        sf_nan_idx = idxnan(typeof(sf))
        
        @test uf_nan_idx > 0
        @test sf_nan_idx > 0
        @test uf_nan_idx != sf_nan_idx  # Should be different
    end
    
    @testset "Index Greater Than Equal Function" begin
        uf = UnsignedFiniteFloat(6, 3)
        values = floats(uf)
        
        # Test value_to_indexgte function if it exists
        # This tests the >= search functionality
        finite_vals = filter(isfinite, values)
        if length(finite_vals) >= 2
            test_val = finite_vals[2]
            
            # Should find the index of value >= test_val
            gte_idx = value_to_indexgte(values, test_val)
            if gte_idx !== nothing
                @test values[gte_idx] >= test_val
                
                # If there's a previous index, it should be < test_val
                if gte_idx > 1
                    @test values[gte_idx - 1] < test_val
                end
            end
        end
    end
    
    @testset "Value to Indices Range" begin
        uf = UnsignedFiniteFloat(6, 3)
        values = floats(uf)
        
        # Test value_to_indices function for range finding
        finite_vals = filter(isfinite, values)
        if length(finite_vals) >= 2
            test_val = (finite_vals[1] + finite_vals[2]) / 2
            
            indices_range = value_to_indices(finite_vals, test_val)
            if indices_range != (nothing, nothing)
                lo, hi = indices_range
                
                if lo !== nothing && hi !== nothing
                    @test lo <= hi
                    @test values[lo] <= test_val <= values[hi]
                end
            end
        end
    end
end

