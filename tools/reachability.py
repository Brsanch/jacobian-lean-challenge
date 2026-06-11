#!/usr/bin/env python3
"""Import-graph reachability sweep for the debloat (2026-06-11).

Computes the transitive import closure of the ROOT modules over the
repo-internal import graph and lists every tracked JacobianChallenge
module NOT in the closure (deletion candidates). Mirrors the
dead-module sweep used by rkirov/jacobian-claude at its endgame.
"""
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

ROOTS = [
    # The challenge implementation (24 items) and its full chain.
    "JacobianChallenge.Basic",
    # Arc-1 durable analysis toolkit (Weyl / IBP / CoV / L2 pairing).
    "JacobianChallenge.Analysis.WeylDBarMollification",
    "JacobianChallenge.Analysis.DBarIntegrationByParts",
    "JacobianChallenge.Analysis.HolomorphicChangeOfVariables",
    "JacobianChallenge.Manifold.L2PairingZeroOneForms",
    # Riemann-sphere end-to-end instantiation (the one per-X demo).
    "JacobianChallenge.Topology.Item14ForRiemannSphere",
    "JacobianChallenge.Manifold.JacobianRiemannSphereInstances",
    "JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances",
    # Substantive closed towers kept regardless of Basic-reachability
    # (durable outputs named in the audit docs):
    # Pompeiu arc: unconditional Cauchy-Pompeiu + chip-4 manifold identity
    # + the leakage identity documenting the Serre wall.
    "JacobianChallenge.Manifold.ChartPompeiuSolutionManifoldIdentity",
    "JacobianChallenge.Manifold.OuterRingLeakage",
    # Residue theorem, unconditional head (RESIDUE_AUDIT.md).
    "JacobianChallenge.Manifold.ResidueTheoremUnconditional",
    # Etale-primitives reverse leg (829a6e8): S2 => genus 0 on arbitrary X.
    "JacobianChallenge.Topology.S2ImpliesGenus0FromEtalePrimitives",
]

def module_of(path: Path) -> str:
    rel = path.relative_to(REPO)
    return str(rel.with_suffix("")).replace("/", ".")

def path_of(module: str) -> Path:
    return REPO / (module.replace(".", "/") + ".lean")

tracked = subprocess.run(
    ["git", "ls-files", "JacobianChallenge/**/*.lean", "JacobianChallenge/*.lean"],
    cwd=REPO, capture_output=True, text=True, check=True,
).stdout.split()
modules = {module_of(REPO / p) for p in tracked}

imp_re = re.compile(r"^import\s+(JacobianChallenge[\w.]*)", re.M)
graph = {}
for m in modules:
    text = path_of(m).read_text(encoding="utf-8", errors="replace")
    graph[m] = [d for d in imp_re.findall(text) if d in modules]

# BFS
seen = set()
stack = [r for r in ROOTS if r in modules]
missing_roots = [r for r in ROOTS if r not in modules]
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    stack.extend(graph[m])

dead = sorted(modules - seen)
print(f"tracked modules: {len(modules)}")
print(f"reachable from roots: {len(seen)}")
print(f"unreachable (deletion candidates): {len(dead)}")
if missing_roots:
    print(f"WARNING missing roots: {missing_roots}", file=sys.stderr)
print("--- DEAD ---")
for m in dead:
    print(m)
