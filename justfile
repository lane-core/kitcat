# kitcat — Cubical Agda library
set shell := ["bash", "-euo", "pipefail", "-c"]

agda := env("AGDA", "agda")

# Typecheck a module (dot-path or file path)
check module:
    #!/usr/bin/env bash
    set -euo pipefail
    mod="{{module}}"
    if [[ "$mod" == *.lagda.md ]]; then
        {{agda}} "$mod"
    elif [[ "$mod" == src/* ]]; then
        {{agda}} "$mod"
    else
        path="src/$(echo "$mod" | tr '.' '/').lagda.md"
        {{agda}} "$path"
    fi

# Measure a module's elaboration time, cold [--total [N]|--internal|--warm]
profile module *flags:
    bin/profile {{module}} {{flags}}

# Normalize expressions in a module's scope and report their size [--quiet]
nf module *exprs:
    bin/nf {{module}} {{exprs}}

# Typecheck every module under a directory (default: whole library), listing failures.
check-tree dir="src":
    #!/usr/bin/env bash
    set -uo pipefail
    dir='{{dir}}'
    if [ ! -d "$dir" ]; then
      echo "check-tree: not a directory: $dir" >&2
      echo "  (arguments are positional: just check-tree src/Test)" >&2
      exit 2
    fi
    files=$(fd '\.lagda(\.[a-z]+)?$' "$dir") || exit 2
    if [ -z "$files" ]; then
      echo "check-tree: no .lagda* modules under $dir" >&2
      exit 2
    fi
    total=$(printf '%s\n' "$files" | wc -l | tr -d ' ')
    fails=$(printf '%s\n' "$files" \
      | xargs -P 8 -I@ sh -c 'agda "$1" >/dev/null 2>&1 || echo "$1"' _ @ | sort)
    if [ -z "$fails" ]; then
      echo "✓ $total modules under $dir typecheck"
    else
      echo "✗ $(printf '%s\n' "$fails" | wc -l | tr -d ' ') of $total failed:"
      printf '%s\n' "$fails" | sed 's|^|  |'
      exit 1
    fi

# Create a new module
new module *flags:
    bin/new-module {{module}} {{flags}}

# Move/rename a module
mv old new *flags:
    bin/mmv {{old}} {{new}} {{flags}}

# Verify resources/ custody: recorded hashes vs vendored artifacts
# (--remote also reports latest arXiv versions for drift)
resources-verify *flags:
    bin/resources-verify {{flags}}
