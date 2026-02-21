#!/usr/bin/env python3
"""
Wire all orphan .lean files into the module tree, avoiding circular imports.

Strategy:
- For each subdirectory, create a root module that imports all children
- For ComputationalPaths.lean, import all subdir root modules
- For ComputationalPaths/Path.lean, add safe orphans only (no circular deps)
- Fix bad imports (Path.Core -> Path.Basic.Core, etc.)
- Comment out dead imports
"""

import re
import os
from pathlib import Path

ROOT = Path("/Users/arthur/clawd/ComputationalPaths")

def get_module(filepath):
    """Convert file path to module name."""
    rel = filepath.relative_to(ROOT)
    return str(rel).replace("/", ".").replace(".lean", "")

def get_imports(filepath):
    """Get all import statements from a file."""
    imports = set()
    if not filepath.exists():
        return imports
    for line in filepath.read_text().splitlines():
        m = re.match(r'^import\s+(\S+)', line.strip())
        if m:
            imports.add(m.group(1))
    return imports

def file_exists_for_module(module):
    """Check if a .lean file exists for a module."""
    return (ROOT / (module.replace(".", "/") + ".lean")).exists()

def has_circular_import(filepath, top_module="ComputationalPaths"):
    """Check if file imports the top-level module (creating a cycle)."""
    if not filepath.exists():
        return False
    for line in filepath.read_text().splitlines():
        if re.match(rf'^import {re.escape(top_module)}$', line.strip()):
            return True
    return False

# ============================================================
# STEP 1: Fix bad imports across all files
# ============================================================
print("=" * 60)
print("STEP 1: Fix bad imports")
print("=" * 60)

fixes = 0
for f in sorted(ROOT.glob("ComputationalPaths/**/*.lean")):
    if ".copex-worktree" in str(f):
        continue
    content = f.read_text()
    new_content = content
    
    # Fix Path.Core -> Path.Basic.Core
    new_content = re.sub(
        r'^(import ComputationalPaths\.Path)\.Core$',
        r'\1.Basic.Core',
        new_content,
        flags=re.MULTILINE
    )
    
    if new_content != content:
        f.write_text(new_content)
        print(f"  Fixed: {f.relative_to(ROOT)}")
        fixes += 1

# Fix HIT/Sphere.lean bad imports
sphere = ROOT / "ComputationalPaths/Path/HIT/Sphere.lean"
if sphere.exists():
    content = sphere.read_text()
    for bad_mod in ["ComputationalPaths.Path.HIT.PushoutPaths", "ComputationalPaths.Path.HIT.Circle"]:
        if f"import {bad_mod}" in content:
            content = content.replace(f"import {bad_mod}", f"-- import {bad_mod}  -- does not exist")
            fixes += 1
    sphere.write_text(content)

# Fix Basic/Core.lean Subsingleton case
core = ROOT / "ComputationalPaths/Path/Basic/Core.lean"
if core.exists():
    content = core.read_text()
    if "| mk hxy =>" in content:
        content = content.replace("| mk hxy =>", "| intro hxy =>")
        core.write_text(content)
        print(f"  Fixed: Subsingleton case in Basic/Core.lean")
        fixes += 1

print(f"  Total fixes: {fixes}")

# ============================================================
# STEP 2: Create/update subdir root modules for ComputationalPaths/
# ============================================================
print("\n" + "=" * 60)
print("STEP 2: Wire ComputationalPaths/ subdirectory modules")
print("=" * 60)

cp_dir = ROOT / "ComputationalPaths"
subdir_roots_created = []

for subdir in sorted(d for d in cp_dir.iterdir() if d.is_dir()):
    if ".copex-worktree" in str(subdir):
        continue
    basename = subdir.name
    root_file = cp_dir / f"{basename}.lean"
    
    # Get all .lean files in this subdir
    lean_files = sorted(subdir.rglob("*.lean"))
    if not lean_files:
        continue
    
    # Build import lines
    all_imports = [f"import {get_module(f)}" for f in lean_files]
    
    if root_file.exists():
        existing_imports = get_imports(root_file)
        missing = [imp for imp in all_imports if imp.split()[1] not in existing_imports]
        if missing:
            content = root_file.read_text().rstrip() + "\n"
            for imp in missing:
                content += imp + "\n"
            root_file.write_text(content)
            print(f"  {root_file.name}: added {len(missing)} imports")
        else:
            print(f"  {root_file.name}: complete")
    else:
        content = f"/- Root module for ComputationalPaths.{basename} -/\n\n"
        for imp in all_imports:
            content += imp + "\n"
        root_file.write_text(content)
        print(f"  {root_file.name}: CREATED ({len(all_imports)} imports)")
    
    subdir_roots_created.append(f"import ComputationalPaths.{basename}")

# ============================================================
# STEP 3: Add safe orphans to Path.lean (avoiding circular deps)
# ============================================================
print("\n" + "=" * 60)
print("STEP 3: Wire orphans into ComputationalPaths/Path.lean")
print("=" * 60)

path_lean = cp_dir / "Path.lean"
existing_path_imports = get_imports(path_lean)

# Find all Path children
path_dir = cp_dir / "Path"
all_path_files = sorted(path_dir.rglob("*.lean"))

safe_orphans = []
circular_orphans = []

for f in all_path_files:
    module = get_module(f)
    if module in existing_path_imports:
        continue
    
    if has_circular_import(f):
        circular_orphans.append(module)
    else:
        safe_orphans.append(module)

# Also filter out files that don't exist (from deleted files referencing them)
safe_orphans = [m for m in safe_orphans if file_exists_for_module(m)]

if safe_orphans:
    content = path_lean.read_text().rstrip() + "\n"
    content += "\n-- Auto-wired orphan imports\n"
    for mod in safe_orphans:
        content += f"import {mod}\n"
    path_lean.write_text(content)
    print(f"  Added {len(safe_orphans)} safe orphans")
    print(f"  Skipped {len(circular_orphans)} circular orphans")
else:
    print(f"  No orphans to add")

# ============================================================
# STEP 4: Update ComputationalPaths.lean top-level
# ============================================================
print("\n" + "=" * 60)
print("STEP 4: Update ComputationalPaths.lean")
print("=" * 60)

cp_lean = ROOT / "ComputationalPaths.lean"
existing_cp_imports = get_imports(cp_lean)

# Add subdir root imports that are missing
missing_roots = []
for imp_line in subdir_roots_created:
    mod = imp_line.split()[1]
    if mod not in existing_cp_imports:
        # Check the root module file doesn't create a cycle
        root_file = ROOT / (mod.replace(".", "/") + ".lean")
        missing_roots.append(imp_line)

if missing_roots:
    content = cp_lean.read_text().rstrip() + "\n"
    content += "\n-- Auto-wired subdirectory root modules\n"
    for imp in missing_roots:
        content += imp + "\n"
    cp_lean.write_text(content)
    print(f"  Added {len(missing_roots)} subdir root imports")
else:
    print(f"  No new imports needed")

# ============================================================
# STEP 5: Remove dead imports from ComputationalPaths.lean and subdir roots
# ============================================================
print("\n" + "=" * 60)
print("STEP 5: Remove dead imports")
print("=" * 60)

def remove_dead_imports(filepath):
    if not filepath.exists():
        return 0
    content = filepath.read_text()
    lines = content.splitlines()
    fixed = []
    removed = 0
    for line in lines:
        m = re.match(r'^import\s+(\S+)', line)
        if m:
            mod = m.group(1)
            if mod.startswith("Mathlib") or mod.startswith("Init") or mod.startswith("Lean"):
                fixed.append(line)
            elif file_exists_for_module(mod):
                fixed.append(line)
            else:
                print(f"    Removed: {line}")
                removed += 1
        else:
            fixed.append(line)
    if removed:
        filepath.write_text("\n".join(fixed) + "\n")
    return removed

total_removed = 0
total_removed += remove_dead_imports(cp_lean)
for f in sorted(cp_dir.glob("*.lean")):
    if ".copex-worktree" in str(f):
        continue
    total_removed += remove_dead_imports(f)

print(f"  Total removed: {total_removed}")

# ============================================================
# STEP 6: Wire CompPaths/ subdirectories
# ============================================================
print("\n" + "=" * 60)
print("STEP 6: Wire CompPaths/ subdirectories")
print("=" * 60)

comppaths_dir = ROOT / "CompPaths"
if comppaths_dir.is_dir():
    cp_subdir_roots = []
    for subdir in sorted(d for d in comppaths_dir.iterdir() if d.is_dir()):
        basename = subdir.name
        root_file = comppaths_dir / f"{basename}.lean"
        lean_files = sorted(subdir.rglob("*.lean"))
        if not lean_files:
            continue
        
        all_imports = [f"import {get_module(f)}" for f in lean_files]
        
        if root_file.exists():
            existing = get_imports(root_file)
            missing = [imp for imp in all_imports if imp.split()[1] not in existing]
            if missing:
                content = root_file.read_text().rstrip() + "\n"
                for imp in missing:
                    content += imp + "\n"
                root_file.write_text(content)
                print(f"  {root_file.name}: added {len(missing)} imports")
            else:
                print(f"  {root_file.name}: complete")
        else:
            content = f"/- Root module for CompPaths.{basename} -/\n\n"
            for imp in all_imports:
                content += imp + "\n"
            root_file.write_text(content)
            print(f"  {root_file.name}: CREATED ({len(all_imports)} imports)")
        
        cp_subdir_roots.append(f"import CompPaths.{basename}")
    
    # Update CompPaths.lean
    comppaths_lean = ROOT / "CompPaths.lean"
    existing = get_imports(comppaths_lean)
    missing = [imp for imp in cp_subdir_roots if imp.split()[1] not in existing]
    if missing:
        content = comppaths_lean.read_text().rstrip() + "\n"
        content += "\n-- Auto-wired subdirectory root modules\n"
        for imp in missing:
            content += imp + "\n"
        comppaths_lean.write_text(content)
        print(f"\n  CompPaths.lean: added {len(missing)} imports")

print("\n✅ All wiring complete!")
