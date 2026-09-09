using SHA: sha256
using TOML: TOML
using JSON: JSON
import P3109Reference as P

const ROOT=normpath(joinpath(@__DIR__, ".."))
function read_tsv(path)
    lines=readlines(path)
    keys=split(first(lines), '\t')
    return [Dict(zip(keys, split(line, '\t'; keepempty = true))) for line in lines[2:end]]
end
function audit()
    inputs=TOML.parsefile(joinpath(ROOT, "inventory", "inputs.toml"))
    source=joinpath(ROOT, inputs["source_root"])
    isdir(source) || error("source verification requires the pinned sibling Maude tree")
    current = Set{String}()
    for (folder, _, source_files) in walkdir(source)
        for name in source_files
            relative = relpath(joinpath(folder, name), source)
            startswith(relative, joinpath("Lean", ".lake")*"/") && continue
            occursin("__pycache__", relative) && continue
            push!(current, relative)
        end
    end
    current == Set(item["path"] for item in inputs["files"]) || error("source file set changed")
    for item in inputs["files"]
        path=joinpath(source, item["path"])
        isfile(path) || error("missing source $(item["path"])")
        bytes2hex(sha256(read(path)))==item["sha256"] || error("source changed: $(item["path"])")
    end
    files=read_tsv(joinpath(ROOT, "inventory", "files.tsv"))
    for row in files
        row["disposition"]=="excluded_generated" && continue
        isfile(joinpath(ROOT, row["target"])) ||
            error("missing disposition target: $(row["target"])")
    end
    rules=read_tsv(joinpath(ROOT, "inventory", "rules.tsv"))
    expected_rules = Set{Tuple{String,String}}()
    for item in inputs["files"]
        endswith(item["path"], ".maude") || continue
        body = read(joinpath(source, item["path"]), String)
        for pattern in (r"\b(?:eq|ceq|mb|cmb)\s+\[([^\]]+)\]", r"\blabel\s+[\w-]+\s+to\s+([\w-]+)")
            for matched in eachmatch(pattern, body)
                push!(expected_rules, (item["path"], String(matched.captures[1])))
            end
        end
    end
    actual_rules = [(row["source"], row["rule"]) for row in rules]
    allunique(actual_rules) && Set(actual_rules) == expected_rules ||
        error("rule mapping coverage changed")
    for row in rules
        isfile(joinpath(ROOT, row["target"])) || error("missing rule target: $(row["target"])")
    end
    operations=read_tsv(joinpath(ROOT, "inventory", "operations.tsv"))
    length(operations)==193 || error("operation count changed")
    allunique(row["source_name"] for row in operations) || error("duplicate operations")
    for row in operations
        n=Symbol(row["source_name"])
        isdefined(P.SpecAPI, n) && Base.ispublic(P.SpecAPI, n) ||
            error("missing public operation $n")
    end
    for name in Base.names(P; all = false, imported = false)
        isdefined(P, name) || error("undefined public package name $name")
    end
    read(joinpath(ROOT, "inventory", "operations.json"))==read(
        joinpath(source, "inventory", "operations.json"),
    ) || error("operation snapshot changed")
    println(
        "PASS provenance: $(length(inputs["files"])) inputs, $(length(files)) dispositions, $(length(rules)) rule/instance mappings, 193 public operations",
    )
    println("KNOWN HISTORICAL DISCREPANCY: ", inputs["historical_discrepancy"])
end
audit()
