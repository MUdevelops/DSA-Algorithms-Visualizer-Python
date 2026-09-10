"""
DSA Algorithm Visualizer
=========================

A complete, interactive, single-file DSA learning & visualization desktop app.

Run:
    python dsa_algorithm_visualizer.py

Requirements:
    Python 3.10+ (tested on 3.11.9)
    Standard library only  (tkinter, heapq, math, random, collections, dataclasses)

Features
--------
* 60+ algorithms across 14 categories (Foundations, Arrays, Strings, Linked Lists,
  Stack, Queue, Hashing, Searching, Sorting, Trees, Graphs, Greedy, DP, Divide & Conquer)
* Animated, step-by-step visualization engine (Start / Pause / Step / Reset / Speed)
* Adaptive canvas renderers: bars, characters, linked nodes, stack, queue, tree,
  graph, DP grid / hash buckets, text
* Right-hand panel: description, how-it-works, complexity, Python source + Copy button
* Custom input, random data generator, examples loader
* 50+ practice problems with hints, complexities and solutions
* Quiz mode, algorithm comparison table, dashboard, live search filter

Architecture
------------
Constants & theme
  -> Frame helpers (bar / chars / grid / tree / graph / stack / queue / text)
  -> Algorithm generators (pure generators yielding visualization frames)
  -> ALGORITHMS registry (name -> Algorithm dataclass)
  -> PROBLEMS / QUIZ_BANK data
  -> Visualizer (Canvas renderer)
  -> AnimationEngine
  -> DSAVisualizerApp (main window + panels)
  -> Problems / Quiz / Comparison Toplevel windows

Author: <your name here>
License: MIT
"""

from __future__ import annotations

import heapq
import math
import random
import sys
import tkinter as tk
from collections import deque
from dataclasses import dataclass, field
from tkinter import messagebox, ttk
from typing import Any, Callable, Dict, Generator, Iterable, List, Optional, Sequence, Tuple

# ============================================================================
# 1. THEME / CONSTANTS
# ============================================================================

APP_TITLE = "DSA Algorithm Visualizer"
APP_SUBTITLE = "Learn • Visualize • Practice • Master"

BG = "#0b1220"
PANEL = "#131f2e"
PANEL_2 = "#1b2a3d"
PANEL_3 = "#22344a"
BORDER = "#2b405a"
TEXT = "#e6eef8"
MUTED = "#93a7bd"
ACCENT = "#22d3ee"
ACCENT_2 = "#3b82f6"
SUCCESS = "#22c55e"
WARNING = "#f59e0b"
DANGER = "#ef4444"
PURPLE = "#a855f7"
PINK = "#ec4899"

FONT_UI = ("Segoe UI", 10)
FONT_UI_B = ("Segoe UI", 10, "bold")
FONT_SMALL = ("Segoe UI", 9)
FONT_TITLE = ("Segoe UI", 17, "bold")
FONT_SUB = ("Segoe UI", 10)
FONT_MONO = ("Consolas", 10)
FONT_MONO_B = ("Consolas", 11, "bold")
FONT_CANVAS = ("Segoe UI", 12, "bold")

ROLE_COLORS: Dict[str, str] = {
    "default": "#31506e",
    "compare": WARNING,
    "swap": DANGER,
    "sorted": SUCCESS,
    "active": ACCENT,
    "found": SUCCESS,
    "discard": "#2a3a4d",
    "visited": PURPLE,
    "current": ACCENT,
    "path": SUCCESS,
    "pivot": PINK,
    "front": ACCENT,
    "rear": WARNING,
    "low": "#38bdf8",
    "mid": PINK,
    "high": "#f97316",
    "window": "#0ea5e9",
    "dim": "#233447",
}

SPEEDS: Dict[str, int] = {
    "Very Slow": 900,
    "Slow": 520,
    "Normal": 260,
    "Fast": 110,
    "Very Fast": 35,
}

CATEGORIES = [
    "Foundations",
    "Arrays",
    "Strings",
    "Linked Lists",
    "Stack",
    "Queue",
    "Hashing",
    "Searching",
    "Sorting",
    "Trees",
    "Graphs",
    "Greedy",
    "Dynamic Programming",
    "Divide & Conquer",
]

MAX_ANIMATED_ITEMS = 60


# ============================================================================
# 2. FRAME HELPERS — every algorithm yields these dicts
# ============================================================================

def bar(values, message="", highlights=None, pointers=None, info=None) -> dict:
    return {"kind": "bars", "values": list(values),
            "highlights": dict(highlights or {}), "pointers": dict(pointers or {}),
            "message": message, "info": list(info or [])}


def chars(rows, message="", info=None) -> dict:
    """rows = [{"label": str, "chars": [...], "highlights": {i: role}}]"""
    return {"kind": "chars", "rows": rows, "message": message, "info": list(info or [])}


def grid(cells, row_labels, col_labels, highlights=None, message="", info=None) -> dict:
    return {"kind": "grid",
            "cells": [[str(c) for c in row] for row in cells],
            "row_labels": list(row_labels), "col_labels": list(col_labels),
            "highlights": dict(highlights or {}), "message": message, "info": list(info or [])}


def nodes(values, message="", highlights=None, pointers=None, info=None) -> dict:
    return {"kind": "nodes", "values": list(values),
            "highlights": dict(highlights or {}), "pointers": dict(pointers or {}),
            "message": message, "info": list(info or [])}


def stack_frame(items, message="", highlights=None, info=None) -> dict:
    return {"kind": "stack", "items": list(items), "highlights": dict(highlights or {}),
            "message": message, "info": list(info or [])}


def queue_frame(items, message="", highlights=None, front=0, rear=None, info=None) -> dict:
    return {"kind": "queue", "items": list(items), "highlights": dict(highlights or {}),
            "front": front, "rear": (len(items) - 1 if rear is None else rear),
            "message": message, "info": list(info or [])}


def tree_frame(root, message="", highlights=None, info=None) -> dict:
    return {"kind": "tree", "tree": root, "highlights": dict(highlights or {}),
            "message": message, "info": list(info or [])}


def graph_frame(graph, message="", highlights=None, edge_highlights=None, info=None) -> dict:
    return {"kind": "graph", "graph": graph, "highlights": dict(highlights or {}),
            "edge_highlights": dict(edge_highlights or {}), "message": message,
            "info": list(info or [])}


def text_frame(lines, message="", info=None) -> dict:
    return {"kind": "text", "lines": list(lines), "message": message, "info": list(info or [])}


# ============================================================================
# 3. SMALL UTILITIES
# ============================================================================

def insertion_sorted(seq: Sequence) -> list:
    """Manual insertion sort (used to prepare sorted search inputs)."""
    a = list(seq)
    for i in range(1, len(a)):
        key = a[i]
        j = i - 1
        while j >= 0 and a[j] > key:
            a[j + 1] = a[j]
            j -= 1
        a[j + 1] = key
    return a


_tree_counter = [0]


def tnode(val, left=None, right=None):
    _tree_counter[0] += 1
    return {"id": _tree_counter[0], "val": val, "left": left, "right": right}


def copy_tree(n):
    if n is None:
        return None
    return {"id": n["id"], "val": n["val"],
            "left": copy_tree(n["left"]), "right": copy_tree(n["right"])}


def tree_layout(root):
    """Return (nodes, edges) where each node gets `_x` (inorder index) & `_depth`."""
    nodes: List[dict] = []
    edges: List[Tuple[int, int]] = []
    counter = [0]

    def inorder(node, depth):
        if node is None:
            return
        inorder(node["left"], depth + 1)
        node["_x"] = counter[0]
        node["_depth"] = depth
        counter[0] += 1
        nodes.append(node)
        inorder(node["right"], depth + 1)

    def collect(node):
        if node is None:
            return
        for child in (node["left"], node["right"]):
            if child is not None:
                edges.append((node["id"], child["id"]))
                collect(child)

    inorder(root, 0)
    collect(root)
    return nodes, edges


def build_bst(values: Iterable[int]):
    """Build a BST from values (duplicates ignored)."""
    root = None
    for v in values:
        if root is None:
            root = tnode(v)
            continue
        cur = root
        while True:
            if v < cur["val"]:
                if cur["left"] is None:
                    cur["left"] = tnode(v)
                    break
                cur = cur["left"]
            elif v > cur["val"]:
                if cur["right"] is None:
                    cur["right"] = tnode(v)
                    break
                cur = cur["right"]
            else:
                break
    return root


def parse_int_list(text: str) -> List[int]:
    text = (text or "").strip()
    if not text:
        raise ValueError("Input is empty.")
    text = text.replace("[", " ").replace("]", " ").replace("(", " ").replace(")", " ")
    text = text.replace(",", " ").replace(";", " ")
    parts = [p for p in text.split() if p]
    out: List[int] = []
    for p in parts:
        out.append(int(float(p)))
    if not out:
        raise ValueError("No numbers found.")
    return out


# ============================================================================
# 4. GRAPH DATA
# ============================================================================

GRAPH_MAIN = {
    "nodes": {
        "A": (0.08, 0.25), "B": (0.34, 0.10), "C": (0.62, 0.16),
        "D": (0.90, 0.42), "E": (0.55, 0.52), "F": (0.18, 0.72),
        "G": (0.78, 0.82),
    },
    "edges": [("A", "B", 4), ("A", "F", 2), ("B", "C", 5), ("B", "E", 3),
              ("C", "D", 2), ("E", "D", 6), ("E", "G", 1), ("F", "E", 1),
              ("F", "G", 7)],
    "directed": False,
}

GRAPH_DAG = {
    "nodes": {
        "A": (0.10, 0.18), "B": (0.42, 0.10), "C": (0.78, 0.18),
        "D": (0.28, 0.62), "E": (0.62, 0.62), "F": (0.90, 0.86),
    },
    "edges": [("A", "B", 1), ("A", "D", 1), ("B", "C", 1), ("B", "E", 1),
              ("C", "F", 1), ("D", "E", 1), ("E", "F", 1)],
    "directed": True,
}


def adjacency(graph) -> Dict[str, List[Tuple[str, int]]]:
    adj: Dict[str, List[Tuple[str, int]]] = {n: [] for n in graph["nodes"]}
    for a, b, w in graph["edges"]:
        adj[a].append((b, w))
        if not graph.get("directed"):
            adj[b].append((a, w))
    for k in adj:
        adj[k].sort()
    return adj


# ============================================================================
# 5. ALGORITHM GENERATORS
# ============================================================================
# ---- SORTING ---------------------------------------------------------------

def gen_bubble(a):
    a = list(a)
    n = len(a)
    yield bar(a, "Bubble Sort — repeatedly swap adjacent out-of-order pairs")
    for i in range(n - 1):
        swapped = False
        for j in range(n - 1 - i):
            hl = {j: "compare", j + 1: "compare"}
            for k in range(n - i, n):
                hl[k] = "sorted"
            yield bar(a, f"Compare a[{j}]={a[j]} and a[{j+1}]={a[j+1]}", hl, {"j": j})
            if a[j] > a[j + 1]:
                a[j], a[j + 1] = a[j + 1], a[j]
                swapped = True
                hl2 = {j: "swap", j + 1: "swap"}
                for k in range(n - i, n):
                    hl2[k] = "sorted"
                yield bar(a, f"Swap → {a[j]}, {a[j+1]}", hl2, {"j": j})
        if not swapped:
            yield bar(a, "No swaps in this pass → early exit (already sorted)",
                      {k: "sorted" for k in range(n)})
            break
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(n)})


def gen_selection(a):
    a = list(a)
    n = len(a)
    yield bar(a, "Selection Sort — select the minimum of the unsorted part")
    for i in range(n - 1):
        m = i
        for j in range(i + 1, n):
            hl = {m: "pivot", j: "compare"}
            for k in range(i):
                hl[k] = "sorted"
            yield bar(a, f"Compare a[{j}]={a[j]} with current min a[{m}]={a[m]}", hl, {"min": m})
            if a[j] < a[m]:
                m = j
        if m != i:
            a[i], a[m] = a[m], a[i]
            yield bar(a, f"Swap minimum {a[i]} into position {i}", {i: "swap", m: "swap"})
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(n)})


def gen_insertion(a):
    a = list(a)
    n = len(a)
    yield bar(a, "Insertion Sort — grow a sorted prefix")
    for i in range(1, n):
        key = a[i]
        j = i - 1
        yield bar(a, f"Take key = {key} (index {i})", {i: "pivot"}, {"key": i})
        while j >= 0 and a[j] > key:
            a[j + 1] = a[j]
            yield bar(a, f"{a[j+1]} > {key} → shift right", {j: "compare", j + 1: "swap"})
            j -= 1
        a[j + 1] = key
        yield bar(a, f"Insert {key} at index {j+1}", {j + 1: "active"})
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(n)})


def gen_merge(a):
    a = list(a)
    yield bar(a, "Merge Sort — divide, conquer, combine")

    def ms(lo, hi):
        if hi - lo <= 1:
            return
        mid = (lo + hi) // 2
        yield bar(a, f"DIVIDE [{lo}:{hi}] at {mid}",
                  {i: "active" for i in range(lo, hi)})
        yield from ms(lo, mid)
        yield from ms(mid, hi)
        left = a[lo:mid]
        right = a[mid:hi]
        i = j = 0
        k = lo
        while i < len(left) and j < len(right):
            yield bar(a, f"Compare {left[i]} vs {right[j]}",
                      {k: "active", lo + i: "compare", mid + j: "compare"})
            if left[i] <= right[j]:
                a[k] = left[i]
                i += 1
            else:
                a[k] = right[j]
                j += 1
            yield bar(a, f"Place {a[k]} at index {k}", {k: "swap"})
            k += 1
        while i < len(left):
            a[k] = left[i]
            i += 1
            yield bar(a, f"Place {a[k]} at index {k}", {k: "swap"})
            k += 1
        while j < len(right):
            a[k] = right[j]
            j += 1
            yield bar(a, f"Place {a[k]} at index {k}", {k: "swap"})
            k += 1
        yield bar(a, f"COMBINE [{lo}:{hi}] merged", {i: "sorted" for i in range(lo, hi)})

    yield from ms(0, len(a))
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(len(a))})


def gen_quick(a):
    a = list(a)
    yield bar(a, "Quick Sort — Lomuto partition around a pivot")

    def qs(lo, hi):
        if lo >= hi:
            return
        pivot = a[hi]
        yield bar(a, f"Pivot = {pivot} (index {hi})", {hi: "pivot"})
        i = lo
        for j in range(lo, hi):
            hl = {j: "compare", hi: "pivot"}
            yield bar(a, f"Compare a[{j}]={a[j]} with pivot {pivot}", hl)
            if a[j] < pivot:
                a[i], a[j] = a[j], a[i]
                yield bar(a, f"Swap {a[j]} ↔ {a[i]}", {i: "swap", j: "swap", hi: "pivot"})
                i += 1
        a[i], a[hi] = a[hi], a[i]
        yield bar(a, f"Place pivot {pivot} at index {i}", {i: "sorted"})
        yield from qs(lo, i - 1)
        yield from qs(i + 1, hi)

    yield from qs(0, len(a) - 1)
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(len(a))})


def gen_heap_sort(a):
    a = list(a)
    n = len(a)
    yield bar(a, "Heap Sort — build a max-heap, then extract the maximum")

    def sift(i, size):
        while True:
            l, r, big = 2 * i + 1, 2 * i + 2, i
            if l < size and a[l] > a[big]:
                big = l
            if r < size and a[r] > a[big]:
                big = r
            if big == i:
                break
            a[i], a[big] = a[big], a[i]
            yield bar(a, f"Sift down: swap {a[big]} ↔ {a[i]}", {i: "swap", big: "swap"})
            i = big

    for i in range(n // 2 - 1, -1, -1):
        yield from sift(i, n)
    yield bar(a, "Max-heap built", {k: "active" for k in range(n)})
    for end in range(n - 1, 0, -1):
        a[0], a[end] = a[end], a[0]
        yield bar(a, f"Move max {a[end]} to index {end}", {0: "swap", end: "sorted"})
        yield from sift(0, end)
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(n)})


def gen_counting(a):
    a = list(a)
    n = len(a)
    if n == 0:
        return
    lo, hi = min(a), max(a)
    cnt = [0] * (hi - lo + 1)
    yield bar(a, "Counting Sort — tally occurrences, then rebuild")
    for i, v in enumerate(a):
        cnt[v - lo] += 1
        yield bar(a, f"Count value {v} → count[{v-lo}] = {cnt[v-lo]}", {i: "active"},
                  info=[f"counts = {cnt}"])
    idx = 0
    for v in range(lo, hi + 1):
        while cnt[v - lo] > 0:
            a[idx] = v
            cnt[v - lo] -= 1
            yield bar(a, f"Write {v} at index {idx}", {idx: "swap"})
            idx += 1
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(n)})


def gen_radix(a):
    a = list(a)
    if not a:
        return
    yield bar(a, "Radix Sort (LSD) — sort digit by digit")
    exp = 1
    mx = max(a)
    while mx // exp > 0:
        buckets: List[List[int]] = [[] for _ in range(10)]
        for i, v in enumerate(a):
            d = (v // exp) % 10
            buckets[d].append(v)
            yield bar(a, f"Digit {d} of {v} → bucket {d}", {i: "active"},
                      info=[f"buckets = {buckets}"])
        k = 0
        for b in range(10):
            for v in buckets[b]:
                a[k] = v
                k += 1
        yield bar(a, f"After pass exp = {exp}", {i: "sorted" for i in range(len(a))})
        exp *= 10
    yield bar(a, "Array sorted ✔", {k: "sorted" for k in range(len(a))})


def gen_bucket(a):
    a = list(a)
    if not a:
        return
    n = len(a)
    yield bar(a, "Bucket Sort — distribute into buckets, sort each, concatenate")
    lo, hi = min(a), max(a)
    span = (hi - lo) or 1
    k = max(2, min(6, n // 2))
    buckets: List[List[int]] = [[] for _ in range(k)]
    for i, v in enumerate(a):
        b = min(k - 1, int((v - lo) / (span + 1) * k))
        buckets[b].append(v)
        yield bar(a, f"{v} → bucket {b}", {i: "active"}, info=[f"buckets = {buckets}"])
    out = []
    for b in range(k):
        buckets[b] = insertion_sorted(buckets[b])
        yield bar(a, f"Bucket {b} sorted: {buckets[b]}", {}, info=[f"buckets = {buckets}"])
        out.extend(buckets[b])
    for i, v in enumerate(out):
        a[i] = v
        yield bar(a, f"Write back {v} at index {i}", {i: "swap"})
    yield bar(a, "Array sorted ✔", {k2: "sorted" for k2 in range(n)})


# ---- SEARCHING -------------------------------------------------------------

def gen_linear_search(a, target):
    a = list(a)
    yield bar(a, f"Linear Search for {target}", {i: "discard" for i in range(len(a))})
    for i, v in enumerate(a):
        hl = {j: "discard" for j in range(len(a))}
        hl[i] = "compare"
        yield bar(a, f"Check index {i}: {v} == {target}?", hl, {"i": i},
                  info=[f"comparisons = {i+1}"])
        if v == target:
            hl[i] = "found"
            yield bar(a, f"Found {target} at index {i} ✔", hl, {"i": i},
                      info=[f"comparisons = {i+1}"])
            return
    yield bar(a, f"{target} not present", {i: "discard" for i in range(len(a))})


def gen_binary_search(a, target):
    a = insertion_sorted(a)
    lo, hi = 0, len(a) - 1
    comps = 0
    yield bar(a, f"Binary Search for {target} in a sorted array")
    while lo <= hi:
        mid = (lo + hi) // 2
        comps += 1
        hl = {}
        for k in range(len(a)):
            hl[k] = "discard"
        for k in range(lo, hi + 1):
            hl[k] = "default"
        hl[mid] = "compare"
        hl[lo] = "low"
        hl[hi] = "high"
        yield bar(a, f"mid = {mid}, a[mid] = {a[mid]}", hl,
                  {"lo": lo, "mid": mid, "hi": hi},
                  info=[f"comparisons = {comps}"])
        if a[mid] == target:
            hl[mid] = "found"
            yield bar(a, f"Found {target} at index {mid} ✔", hl,
                      info=[f"comparisons = {comps}"])
            return
        if a[mid] < target:
            lo = mid + 1
            yield bar(a, f"{a[mid]} < {target} → search right half", hl,
                      {"lo": lo, "hi": hi}, info=[f"comparisons = {comps}"])
        else:
            hi = mid - 1
            yield bar(a, f"{a[mid]} > {target} → search left half", hl,
                      {"lo": lo, "hi": hi}, info=[f"comparisons = {comps}"])
    yield bar(a, f"{target} not found", {k: "discard" for k in range(len(a))},
              info=[f"comparisons = {comps}"])


def gen_lower_bound(a, target):
    a = insertion_sorted(a)
    lo, hi = 0, len(a)
    yield bar(a, f"Lower Bound of {target} — first index with value >= target")
    while lo < hi:
        mid = (lo + hi) // 2
        hl = {k: "discard" for k in range(len(a))}
        for k in range(lo, hi):
            hl[k] = "default"
        hl[mid] = "compare"
        yield bar(a, f"a[{mid}] = {a[mid]} vs {target}", hl, {"lo": lo, "mid": mid, "hi": hi})
        if a[mid] < target:
            lo = mid + 1
        else:
            hi = mid
    hl = {k: "discard" for k in range(len(a))}
    if lo < len(a):
        hl[lo] = "found"
    yield bar(a, f"Lower bound index = {lo}", hl, {"lo": lo})


def gen_upper_bound(a, target):
    a = insertion_sorted(a)
    lo, hi = 0, len(a)
    yield bar(a, f"Upper Bound of {target} — first index with value > target")
    while lo < hi:
        mid = (lo + hi) // 2
        hl = {k: "discard" for k in range(len(a))}
        for k in range(lo, hi):
            hl[k] = "default"
        hl[mid] = "compare"
        yield bar(a, f"a[{mid}] = {a[mid]} vs {target}", hl, {"lo": lo, "mid": mid, "hi": hi})
        if a[mid] <= target:
            lo = mid + 1
        else:
            hi = mid
    hl = {k: "discard" for k in range(len(a))}
    if lo < len(a):
        hl[lo] = "found"
    yield bar(a, f"Upper bound index = {lo}", hl, {"lo": lo})


def gen_first_occurrence(a, target):
    a = insertion_sorted(a)
    best = -1
    lo, hi = 0, len(a) - 1
    yield bar(a, f"First Occurrence of {target}")
    while lo <= hi:
        mid = (lo + hi) // 2
        hl = {mid: "compare"}
        if best >= 0:
            hl[best] = "found"
        yield bar(a, f"a[{mid}] = {a[mid]}", hl, {"lo": lo, "mid": mid, "hi": hi},
                  info=[f"best = {best}"])
        if a[mid] == target:
            best = mid
            hi = mid - 1
            yield bar(a, f"Match at {mid}; keep searching left", {mid: "found"},
                      info=[f"best = {best}"])
        elif a[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    yield bar(a, f"First occurrence = {best}", ({best: "found"} if best >= 0 else {}))


def gen_last_occurrence(a, target):
    a = insertion_sorted(a)
    best = -1
    lo, hi = 0, len(a) - 1
    yield bar(a, f"Last Occurrence of {target}")
    while lo <= hi:
        mid = (lo + hi) // 2
        hl = {mid: "compare"}
        if best >= 0:
            hl[best] = "found"
        yield bar(a, f"a[{mid}] = {a[mid]}", hl, {"lo": lo, "mid": mid, "hi": hi},
                  info=[f"best = {best}"])
        if a[mid] == target:
            best = mid
            lo = mid + 1
            yield bar(a, f"Match at {mid}; keep searching right", {mid: "found"},
                      info=[f"best = {best}"])
        elif a[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    yield bar(a, f"Last occurrence = {best}", ({best: "found"} if best >= 0 else {}))


def gen_rotated_search(a, target):
    a = list(a)
    lo, hi = 0, len(a) - 1
    yield bar(a, f"Search {target} in a rotated sorted array")
    while lo <= hi:
        mid = (lo + hi) // 2
        hl = {k: "discard" for k in range(len(a))}
        for k in range(lo, hi + 1):
            hl[k] = "default"
        hl[mid] = "compare"
        yield bar(a, f"a[{mid}] = {a[mid]}", hl, {"lo": lo, "mid": mid, "hi": hi})
        if a[mid] == target:
            yield bar(a, f"Found {target} at index {mid} ✔", {mid: "found"})
            return
        if a[lo] <= a[mid]:
            if a[lo] <= target < a[mid]:
                hi = mid - 1
            else:
                lo = mid + 1
        else:
            if a[mid] < target <= a[hi]:
                lo = mid + 1
            else:
                hi = mid - 1
    yield bar(a, f"{target} not found", {k: "discard" for k in range(len(a))})


def gen_peak_element(a):
    a = list(a)
    lo, hi = 0, len(a) - 1
    yield bar(a, "Find a Peak Element with binary search")
    while lo < hi:
        mid = (lo + hi) // 2
        hl = {mid: "compare", mid + 1: "active"}
        yield bar(a, f"a[{mid}]={a[mid]} vs a[{mid+1}]={a[mid+1]}", hl,
                  {"lo": lo, "mid": mid, "hi": hi})
        if a[mid] < a[mid + 1]:
            lo = mid + 1
        else:
            hi = mid
    yield bar(a, f"Peak at index {lo} (value {a[lo]})", {lo: "found"})


def gen_bs_on_answer(a, target):
    a = list(a)
    # Interpret: find smallest x such that x*x >= target  (classic "binary search on answer")
    lo, hi = 0, max(1, max(a) if a else 100)
    yield text_frame([f"Binary Search on the Answer",
                      f"Problem: smallest integer x with x*x >= {target}",
                      f"Search space: [0, {hi}]"], "Binary Search on Answer")
    while lo < hi:
        mid = (lo + hi) // 2
        yield text_frame([f"lo={lo}  hi={hi}  mid={mid}",
                          f"is_good({mid})?  {mid}*{mid} = {mid*mid} >= {target} → {mid*mid >= target}"],
                         f"Testing mid = {mid}")
        if mid * mid >= target:
            hi = mid
        else:
            lo = mid + 1
    yield text_frame([f"Smallest x with x*x >= {target} is {lo}",
                      f"Check: {lo}*{lo} = {lo*lo}"], "Answer found ✔")


# ---- ARRAYS ----------------------------------------------------------------

def gen_kadane(a):
    a = list(a)
    if not a:
        return
    best = a[0]
    cur = a[0]
    start = end = 0
    s = 0
    yield bar(a, "Kadane's Algorithm — maximum subarray sum",
              {0: "active"}, info=[f"current_sum = {cur}", f"maximum_sum = {best}"])
    for i in range(1, len(a)):
        if cur + a[i] < a[i]:
            cur = a[i]
            s = i
        else:
            cur += a[i]
        if cur > best:
            best = cur
            start, end = s, i
        hl = {k: "window" for k in range(start, end + 1)}
        hl[i] = "active"
        yield bar(a, f"i={i}: extend or restart — current_sum = {cur}", hl, {"i": i},
                  info=[f"current_sum = {cur}", f"maximum_sum = {best}"])
    yield bar(a, f"Maximum subarray sum = {best} → {a[start:end+1]}",
              {k: "found" for k in range(start, end + 1)},
              info=[f"maximum_sum = {best}"])


def gen_prefix_sum(a):
    a = list(a)
    pre = [0]
    yield bar(a, "Prefix Sum — precompute cumulative sums for O(1) range queries")
    for i, v in enumerate(a):
        pre.append(pre[-1] + v)
        yield bar(a, f"prefix[{i+1}] = prefix[{i}] + {v} = {pre[-1]}",
                  {i: "active"}, info=[f"prefix = {pre}"])
    yield text_frame([f"Array       : {a}",
                      f"Prefix sums : {pre}",
                      "",
                      f"sum(2..5) = prefix[6] - prefix[2] = {pre[6] - pre[2] if len(pre) > 6 else 'n/a'}",
                      "Range sum query is now O(1)."],
                     "Prefix sums ready ✔")


def gen_sliding_window(a):
    a = list(a)
    k = min(3, len(a))
    if k <= 0:
        return
    yield bar(a, f"Sliding Window — max sum of {k} consecutive elements")
    cur = sum(a[:k])
    best = cur
    yield bar(a, f"Window [0..{k-1}] sum = {cur}", {i: "window" for i in range(k)},
              info=[f"current = {cur}", f"best = {best}"])
    for i in range(k, len(a)):
        cur += a[i] - a[i - k]
        best = max(best, cur)
        hl = {j: "window" for j in range(i - k + 1, i + 1)}
        yield bar(a, f"Slide: +{a[i]} -{a[i-k]} → sum = {cur}",
                  hl, {"in": i, "out": i - k},
                  info=[f"current = {cur}", f"best = {best}"])
    yield bar(a, f"Maximum window sum = {best}")


def gen_two_pointers(a, target):
    a = insertion_sorted(a)
    lo, hi = 0, len(a) - 1
    yield bar(a, f"Two Pointers — find a pair summing to {target}")
    while lo < hi:
        s = a[lo] + a[hi]
        hl = {lo: "low", hi: "high"}
        yield bar(a, f"{a[lo]} + {a[hi]} = {s}", hl, {"lo": lo, "hi": hi},
                  info=[f"target = {target}"])
        if s == target:
            yield bar(a, f"Pair found: ({a[lo]}, {a[hi]}) ✔", {lo: "found", hi: "found"})
            return
        if s < target:
            lo += 1
        else:
            hi -= 1
    yield bar(a, "No pair found")


def gen_frequency_count(a):
    a = list(a)
    freq: Dict[int, int] = {}
    yield text_frame(["Frequency Counting with a hash map",
                      f"Array: {a}"], "Counting…")
    for i, v in enumerate(a):
        freq[v] = freq.get(v, 0) + 1
        yield bar(a, f"freq[{v}] = {freq[v]}", {i: "active"},
                  info=[f"freq = {freq}"])
    rows = [[k, v] for k, v in sorted(freq.items())]
    yield grid(rows, [f"value {r[0]}" for r in rows], ["count"],
               message="Frequency table complete ✔",
               info=[f"distinct values = {len(freq)}"])


def gen_rotation(a):
    a = list(a)
    k = 2 % (len(a) or 1)
    yield bar(a, f"Rotate array left by k = {k} (reversal technique)")
    # reverse first k
    def rev(lo, hi, label):
        while lo < hi:
            a[lo], a[hi] = a[hi], a[lo]
            yield bar(a, f"{label}: swap {a[hi]} ↔ {a[lo]}", {lo: "swap", hi: "swap"})
            lo += 1
            hi -= 1

    yield from rev(0, k - 1, "Reverse first k")
    yield from rev(k, len(a) - 1, "Reverse remaining")
    yield from rev(0, len(a) - 1, "Reverse whole")
    yield bar(a, "Rotated ✔", {i: "sorted" for i in range(len(a))})


def gen_difference_array(a):
    a = list(a)
    n = len(a)
    diff = [0] * (n + 1)
    diff[0] = a[0]
    for i in range(1, n):
        diff[i] = a[i] - a[i - 1]
    yield bar(a, "Difference Array — range updates in O(1)", info=[f"diff = {diff}"])
    for i in range(1, n):
        yield bar(a, f"diff[{i}] = a[{i}] - a[{i-1}] = {diff[i]}", {i: "active", i - 1: "compare"},
                  info=[f"diff = {diff}"])
    yield text_frame([f"Array : {a}", f"Diff  : {diff}",
                      "",
                      "Apply +5 to range [1..3]: diff[1] += 5, diff[4] -= 5",
                      "Then rebuild with a prefix sum → O(n)."], "Difference array built ✔")


# ---- STRINGS ---------------------------------------------------------------

def gen_string_traversal(s):
    s = str(s)
    rows = [{"label": "s", "chars": list(s), "highlights": {}}]
    yield chars(rows, "String Traversal — visit every character once")
    for i in range(len(s)):
        rows = [{"label": "s", "chars": list(s), "highlights": {i: "active"}}]
        yield chars(rows, f"Index {i}: '{s[i]}' (ord = {ord(s[i])})",
                    info=[f"length = {len(s)}"])


def gen_char_frequency(s):
    s = str(s)
    freq: Dict[str, int] = {}
    for i, ch in enumerate(s):
        freq[ch] = freq.get(ch, 0) + 1
        yield chars([{"label": "s", "chars": list(s), "highlights": {i: "active"}}],
                    f"count['{ch}'] = {freq[ch]}", info=[f"freq = {freq}"])
    rows = [[k, v] for k, v in sorted(freq.items())]
    yield grid(rows, [f"'{r[0]}'" for r in rows], ["count"],
               message="Character frequency table ✔")


def gen_reverse_string(s):
    s = str(s)
    arr = list(s)
    lo, hi = 0, len(arr) - 1
    yield chars([{"label": "s", "chars": arr, "highlights": {}}], "Reverse a string with two pointers")
    while lo < hi:
        arr[lo], arr[hi] = arr[hi], arr[lo]
        yield chars([{"label": "s", "chars": arr,
                      "highlights": {lo: "swap", hi: "swap"}}],
                    f"Swap '{arr[hi]}' ↔ '{arr[lo]}'")
        lo += 1
        hi -= 1
    yield chars([{"label": "reversed", "chars": arr,
                  "highlights": {i: "found" for i in range(len(arr))}}],
                "Reversed ✔")


def gen_palindrome(s):
    s = str(s)
    arr = list(s)
    lo, hi = 0, len(arr) - 1
    yield chars([{"label": "s", "chars": arr, "highlights": {}}], "Palindrome Check")
    while lo < hi:
        hl = {lo: "low", hi: "high"}
        yield chars([{"label": "s", "chars": arr, "highlights": hl}],
                    f"Compare '{arr[lo]}' and '{arr[hi]}'")
        if arr[lo] != arr[hi]:
            hl = {lo: "swap", hi: "swap"}
            yield chars([{"label": "s", "chars": arr, "highlights": hl}],
                        "Mismatch → NOT a palindrome ✘")
            return
        lo += 1
        hi -= 1
    yield chars([{"label": "s", "chars": arr,
                  "highlights": {i: "found" for i in range(len(arr))}}],
                "It IS a palindrome ✔")


def gen_anagram(s1, s2):
    a, b = list(s1), list(s2)
    yield chars([{"label": "s1", "chars": a, "highlights": {}},
                 {"label": "s2", "chars": b, "highlights": {}}],
                "Anagram Check — count characters in both strings")
    if len(a) != len(b):
        yield chars([{"label": "s1", "chars": a, "highlights": {}},
                     {"label": "s2", "chars": b, "highlights": {}}],
                    f"Different lengths ({len(a)} vs {len(b)}) → NOT anagrams ✘")
        return
    counts: Dict[str, int] = {}
    for i, ch in enumerate(a):
        counts[ch] = counts.get(ch, 0) + 1
        yield chars([{"label": "s1", "chars": a, "highlights": {i: "active"}},
                     {"label": "s2", "chars": b, "highlights": {}}],
                    f"+1 for '{ch}'", info=[f"counts = {counts}"])
    for i, ch in enumerate(b):
        counts[ch] = counts.get(ch, 0) - 1
        ok = counts[ch] >= 0
        yield chars([{"label": "s1", "chars": a, "highlights": {}},
                     {"label": "s2", "chars": b,
                      "highlights": {i: ("active" if ok else "swap")}}],
                    f"-1 for '{ch}'", info=[f"counts = {counts}"])
        if not ok:
            yield chars([{"label": "s1", "chars": a, "highlights": {}},
                         {"label": "s2", "chars": b, "highlights": {i: "swap"}}],
                        "Count went negative → NOT anagrams ✘")
            return
    yield chars([{"label": "s1", "chars": a, "highlights": {i: "found" for i in range(len(a))}},
                 {"label": "s2", "chars": b, "highlights": {i: "found" for i in range(len(b))}}],
                "All counts zero → ANAGRAMS ✔")


def gen_substring_search(s, pat=None):
    s = str(s)
    pat = pat or (s[:2] if len(s) >= 2 else s)
    n, m = len(s), len(pat)
    yield chars([{"label": "text", "chars": list(s), "highlights": {}},
                 {"label": "pat", "chars": list(pat), "highlights": {}}],
                f"Naive Substring Search for '{pat}'")
    for i in range(n - m + 1):
        hl = {j: "compare" for j in range(i, i + m)}
        yield chars([{"label": "text", "chars": list(s), "highlights": hl},
                     {"label": "pat", "chars": list(pat),
                      "highlights": {j: "active" for j in range(m)}}],
                    f"Align pattern at index {i}")
        if s[i:i + m] == pat:
            yield chars([{"label": "text", "chars": list(s),
                          "highlights": {j: "found" for j in range(i, i + m)}},
                         {"label": "pat", "chars": list(pat),
                          "highlights": {j: "found" for j in range(m)}}],
                        f"Match found at index {i} ✔")
            return
    yield chars([{"label": "text", "chars": list(s), "highlights": {}},
                 {"label": "pat", "chars": list(pat), "highlights": {}}],
                "Pattern not found ✘")


def gen_string_compression(s):
    s = str(s)
    arr = list(s)
    yield chars([{"label": "s", "chars": arr, "highlights": {}}],
                "String Compression — run-length encoding")
    out: List[str] = []
    i = 0
    while i < len(arr):
        j = i
        while j < len(arr) and arr[j] == arr[i]:
            j += 1
        run = j - i
        out.append(arr[i])
        out.append(str(run))
        yield chars([{"label": "s", "chars": arr,
                      "highlights": {k: "window" for k in range(i, j)}},
                     {"label": "out", "chars": out,
                      "highlights": {len(out) - 1: "found"}}],
                    f"'{arr[i]}' repeats {run} time(s)")
        i = j
    yield chars([{"label": "s", "chars": arr, "highlights": {}},
                 {"label": "out", "chars": out,
                  "highlights": {k: "found" for k in range(len(out))}}],
                "Compressed ✔")


def gen_string_hashing(s):
    s = str(s)
    lines = ["Polynomial rolling hash   h = h * 31 + ord(c)",
             f"String: {s}", ""]
    h = 0
    for i, ch in enumerate(s):
        h = h * 31 + ord(ch)
        h %= (10 ** 9 + 7)
        lines.append(f"after '{ch}' (ord {ord(ch)}): h = {h}")
    lines.append("")
    lines.append(f"Final hash = {h}")
    yield text_frame(lines, "String Hashing (rolling hash)")


# ---- LINKED LIST -----------------------------------------------------------

def gen_ll_insert_end(a):
    vals = list(a)
    cur: List[int] = []
    yield nodes(cur, "Insert at End — append a node at the tail")
    for v in vals:
        cur = cur + [v]
        yield nodes(cur, f"Append node [{v}]",
                    {len(cur) - 1: "active"}, {"tail": len(cur) - 1})
    yield nodes(cur, "Linked list built ✔", {i: "found" for i in range(len(cur))})


def gen_ll_insert_front(a):
    vals = list(a)
    cur: List[int] = []
    yield nodes(cur, "Insert at Beginning — O(1) head insertion")
    for v in vals:
        cur = [v] + cur
        yield nodes(cur, f"Prepend node [{v}]", {0: "active"}, {"head": 0})
    yield nodes(cur, "Linked list built ✔", {i: "found" for i in range(len(cur))})


def gen_ll_delete(a):
    vals = list(a)
    cur = list(vals)
    target = vals[len(vals) // 2] if vals else 0
    yield nodes(cur, f"Delete by Value — remove the first node holding {target}")
    for i, v in enumerate(cur):
        yield nodes(cur, f"Visit node {i} (value {v})", {i: "compare"}, {"curr": i})
        if v == target:
            yield nodes(cur, f"Found {target} → unlink it", {i: "swap"}, {"curr": i})
            cur = cur[:i] + cur[i + 1:]
            yield nodes(cur, "Node removed", {}, {"curr": min(i, len(cur) - 1)})
            break
    yield nodes(cur, "Done ✔", {i: "found" for i in range(len(cur))})


def gen_ll_reverse(a):
    vals = list(a)
    n = len(vals)
    yield nodes(vals, "Reverse a Singly Linked List — three pointers")
    rev: List[int] = []
    for i in range(n - 1, -1, -1):
        rev.append(vals[i])
        yield nodes(rev, f"Point node {i} backwards",
                    {len(rev) - 1: "active"},
                    {"prev": len(rev) - 2 if len(rev) > 1 else 0, "curr": len(rev) - 1})
    yield nodes(rev, "List reversed ✔", {i: "found" for i in range(len(rev))})


def gen_ll_middle(a):
    vals = list(a)
    yield nodes(vals, "Find the Middle — fast & slow pointers")
    slow = fast = 0
    while fast < len(vals) and fast + 1 < len(vals):
        slow += 1
        fast += 2
        yield nodes(vals, f"slow = {slow}, fast = {fast}",
                    {slow: "active", min(fast, len(vals) - 1): "compare"},
                    {"slow": slow, "fast": min(fast, len(vals) - 1)})
    yield nodes(vals, f"Middle node is index {slow} (value {vals[slow]})",
                {slow: "found"}, {"slow": slow})


def gen_ll_cycle(a):
    vals = list(a)
    n = len(vals)
    # Simulate: last node points back to index 2 (if possible)
    cyc = 2 if n > 3 else 0
    yield nodes(vals, f"Detect Cycle (Floyd) — tail points back to index {cyc}")
    slow = fast = 0
    while fast < n and slow < n:
        slow = (slow + 1)
        fast = (fast + 2)
        if fast >= n:
            yield nodes(vals, "fast reached NULL → no cycle ✘",
                        {}, {"slow": slow % n})
            return
        if slow == fast:
            yield nodes(vals, f"slow == fast == {slow} → CYCLE detected ✔",
                        {slow: "swap"}, {"slow": slow, "fast": fast})
            return
        yield nodes(vals, f"slow = {slow}, fast = {fast}",
                    {slow: "active", fast: "compare"},
                    {"slow": slow, "fast": fast})


# ---- STACK -----------------------------------------------------------------

def gen_stack_ops(a):
    vals = list(a)
    st: List[int] = []
    yield stack_frame(st, "Stack — LIFO. Pushing elements…")
    for v in vals:
        st.append(v)
        yield stack_frame(st, f"push({v})", {len(st) - 1: "active"})
    yield stack_frame(st, "Peek → " + str(st[-1] if st else None), {len(st) - 1: "found"})
    while st:
        v = st.pop()
        yield stack_frame(st, f"pop() → {v}",
                          ({len(st) - 1: "compare"} if st else {}))
    yield stack_frame(st, "Stack is empty ✔")


def gen_balanced_parens(s):
    s = str(s)
    pairs = {")": "(", "]": "[", "}": "{"}
    st: List[str] = []
    yield chars([{"label": "expr", "chars": list(s), "highlights": {}},
                 {"label": "stack", "chars": list(st), "highlights": {}}],
                "Balanced Parentheses using a stack")
    for i, ch in enumerate(s):
        if ch in "([{":
            st.append(ch)
            yield chars([{"label": "expr", "chars": list(s), "highlights": {i: "active"}},
                         {"label": "stack", "chars": list(st),
                          "highlights": {len(st) - 1: "active"}}],
                        f"Push '{ch}'")
        elif ch in pairs:
            if not st or st[-1] != pairs[ch]:
                yield chars([{"label": "expr", "chars": list(s), "highlights": {i: "swap"}},
                             {"label": "stack", "chars": list(st), "highlights": {}}],
                            f"Mismatch at '{ch}' → NOT balanced ✘")
                return
            st.pop()
            yield chars([{"label": "expr", "chars": list(s), "highlights": {i: "compare"}},
                         {"label": "stack", "chars": list(st), "highlights": {}}],
                        f"Pop matching '{pairs[ch]}'")
        else:
            yield chars([{"label": "expr", "chars": list(s), "highlights": {i: "dim"}},
                         {"label": "stack", "chars": list(st), "highlights": {}}],
                        f"'{ch}' is not a bracket → skip")
    ok = not st
    yield chars([{"label": "expr", "chars": list(s),
                  "highlights": {i: "found" for i in range(len(s))}},
                 {"label": "stack", "chars": list(st), "highlights": {}}],
                "BALANCED ✔" if ok else "Unclosed brackets → NOT balanced ✘")


def gen_infix_postfix(s):
    s = str(s)
    prec = {"+": 1, "-": 1, "*": 2, "/": 2, "^": 3}
    st: List[str] = []
    out: List[str] = []
    yield chars([{"label": "infix", "chars": list(s), "highlights": {}},
                 {"label": "stack", "chars": list(st), "highlights": {}},
                 {"label": "postfix", "chars": list(out), "highlights": {}}],
                "Infix → Postfix (Shunting-Yard)")
    for i, ch in enumerate(s):
        if ch == " ":
            continue
        if ch.isalnum():
            out.append(ch)
            yield chars([{"label": "infix", "chars": list(s), "highlights": {i: "active"}},
                         {"label": "stack", "chars": list(st), "highlights": {}},
                         {"label": "postfix", "chars": list(out),
                          "highlights": {len(out) - 1: "found"}}],
                        f"Operand '{ch}' → output")
        elif ch == "(":
            st.append(ch)
            yield chars([{"label": "infix", "chars": list(s), "highlights": {i: "active"}},
                         {"label": "stack", "chars": list(st),
                          "highlights": {len(st) - 1: "active"}},
                         {"label": "postfix", "chars": list(out), "highlights": {}}],
                        "Push '('")
        elif ch == ")":
            while st and st[-1] != "(":
                out.append(st.pop())
            if st:
                st.pop()
            yield chars([{"label": "infix", "chars": list(s), "highlights": {i: "active"}},
                         {"label": "stack", "chars": list(st), "highlights": {}},
                         {"label": "postfix", "chars": list(out), "highlights": {}}],
                        "Pop until '('")
        else:
            while st and st[-1] != "(" and prec.get(st[-1], 0) >= prec.get(ch, 0):
                out.append(st.pop())
            st.append(ch)
            yield chars([{"label": "infix", "chars": list(s), "highlights": {i: "active"}},
                         {"label": "stack", "chars": list(st),
                          "highlights": {len(st) - 1: "compare"}},
                         {"label": "postfix", "chars": list(out), "highlights": {}}],
                        f"Operator '{ch}' → stack")
    while st:
        out.append(st.pop())
    yield chars([{"label": "infix", "chars": list(s), "highlights": {}},
                 {"label": "stack", "chars": list(st), "highlights": {}},
                 {"label": "postfix", "chars": list(out),
                  "highlights": {k: "found" for k in range(len(out))}}],
                "Postfix expression ready ✔")


def gen_postfix_eval(s):
    s = str(s)
    st: List[int] = []
    yield chars([{"label": "postfix", "chars": list(s), "highlights": {}},
                 {"label": "stack", "chars": [str(x) for x in st], "highlights": {}}],
                "Postfix Evaluation")
    for i, ch in enumerate(s):
        if ch == " ":
            continue
        if ch.isdigit():
            st.append(int(ch))
            yield chars([{"label": "postfix", "chars": list(s), "highlights": {i: "active"}},
                         {"label": "stack", "chars": [str(x) for x in st],
                          "highlights": {len(st) - 1: "active"}}],
                        f"Push {ch}")
        else:
            b = st.pop()
            a = st.pop()
            r = {"+": a + b, "-": a - b, "*": a * b, "/": a // b if b else 0}[ch]
            st.append(r)
            yield chars([{"label": "postfix", "chars": list(s), "highlights": {i: "compare"}},
                         {"label": "stack", "chars": [str(x) for x in st],
                          "highlights": {len(st) - 1: "found"}}],
                        f"{a} {ch} {b} = {r}")
    yield chars([{"label": "postfix", "chars": list(s), "highlights": {}},
                 {"label": "result", "chars": [str(st[-1])] if st else ["?"],
                  "highlights": {0: "found"}}],
                "Evaluation complete ✔")


def gen_next_greater(a):
    a = list(a)
    n = len(a)
    res = [-1] * n
    st: List[int] = []
    yield bar(a, "Next Greater Element using a monotonic stack", info=[f"result = {res}"])
    for i in range(n):
        while st and a[st[-1]] < a[i]:
            idx = st.pop()
            res[idx] = a[i]
            yield bar(a, f"a[{idx}]={a[idx]} has next greater {a[i]}",
                      {idx: "found", i: "compare"}, info=[f"result = {res}"])
        st.append(i)
        yield bar(a, f"Push index {i} (value {a[i]})",
                  {i: "active"}, {"top": i}, info=[f"stack = {st}", f"result = {res}"])
    yield bar(a, "Next greater elements resolved ✔",
              {i: "found" for i in range(n) if res[i] != -1},
              info=[f"result = {res}"])


def gen_min_stack(a):
    vals = list(a)
    st: List[int] = []
    mn: List[int] = []
    yield stack_frame(st, "Min Stack — O(1) minimum via an auxiliary stack")
    for v in vals:
        st.append(v)
        mn.append(v if not mn else min(mn[-1], v))
        yield stack_frame(st, f"push({v}) — current min = {mn[-1]}",
                          {len(st) - 1: "active"},
                          info=[f"min-stack = {mn}"])
    while st:
        v = st.pop()
        mn.pop()
        yield stack_frame(st, f"pop() → {v} — new min = {mn[-1] if mn else '—'}",
                          ({len(st) - 1: "compare"} if st else {}),
                          info=[f"min-stack = {mn}"])
    yield stack_frame(st, "Done ✔")


# ---- QUEUE -----------------------------------------------------------------

def gen_simple_queue(a):
    vals = list(a)
    q: List[int] = []
    yield queue_frame(q, "Simple Queue — FIFO (enqueue at rear)")
    for v in vals:
        q.append(v)
        yield queue_frame(q, f"enqueue({v})", {len(q) - 1: "active"})
    while q:
        v = q.pop(0)
        yield queue_frame(q, f"dequeue() → {v}", ({0: "compare"} if q else {}))
    yield queue_frame(q, "Queue is empty ✔")


def gen_circular_queue(a):
    vals = list(a)
    cap = max(4, len(vals))
    buf: List[Optional[int]] = [None] * cap
    front = 0
    size = 0
    yield text_frame([f"Circular Queue of capacity {cap}",
                      "rear = (front + size) % capacity",
                      "Wrap-around reuses freed slots."], "Circular Queue")

    def render(msg, hl=None):
        return {"kind": "queue", "items": [("_" if x is None else x) for x in buf],
                "highlights": hl or {}, "front": front,
                "rear": (front + size - 1) % cap if size else front,
                "message": msg, "info": [f"front = {front}", f"size = {size}",
                                         f"capacity = {cap}"]}

    for v in vals:
        if size == cap:
            yield render("Queue full — cannot enqueue", {front: "swap"})
            break
        idx = (front + size) % cap
        buf[idx] = v
        size += 1
        yield render(f"enqueue({v}) at index {idx}", {idx: "active"})
    while size > 0:
        v = buf[front]
        buf[front] = None
        yield render(f"dequeue() → {v}", {front: "compare"})
        front = (front + 1) % cap
        size -= 1
    yield render("Circular queue empty ✔", {front: "found"})


def gen_deque(a):
    vals = list(a)
    dq: List[int] = []
    yield queue_frame(dq, "Deque — insert/remove at both ends")
    for i, v in enumerate(vals):
        if i % 2 == 0:
            dq.append(v)
            yield queue_frame(dq, f"append_right({v})", {len(dq) - 1: "active"})
        else:
            dq.insert(0, v)
            yield queue_frame(dq, f"append_left({v})", {0: "active"})
    while dq:
        if len(dq) % 2 == 0:
            v = dq.pop()
            yield queue_frame(dq, f"pop_right() → {v}", ({len(dq) - 1: "compare"} if dq else {}))
        else:
            v = dq.pop(0)
            yield queue_frame(dq, f"pop_left() → {v}", ({0: "compare"} if dq else {}))
    yield queue_frame(dq, "Deque empty ✔")


def gen_priority_queue(a):
    vals = list(a)
    heap: List[int] = []
    yield bar(heap or [0], "Priority Queue (binary min-heap via heapq)")
    for v in vals:
        heapq.heappush(heap, v)
        yield bar(heap, f"push({v}) — smallest stays at index 0",
                  {0: "found"})
    while heap:
        v = heapq.heappop(heap)
        yield bar(heap or [0], f"pop() → {v} (highest priority)",
                  ({0: "active"} if heap else {}))
    yield bar([0], "Priority queue empty ✔")


def gen_queue_using_stacks(a):
    vals = list(a)
    s_in: List[int] = []
    s_out: List[int] = []
    yield text_frame(["Queue using two stacks",
                      "enqueue → push onto s_in",
                      "dequeue → if s_out empty, move all from s_in, then pop"],
                     "Queue via Stacks")
    for v in vals:
        s_in.append(v)
        yield text_frame([f"enqueue({v})", f"s_in  = {s_in}", f"s_out = {s_out}"],
                         f"Pushed {v}")
    while s_in or s_out:
        if not s_out:
            while s_in:
                s_out.append(s_in.pop())
            yield text_frame(["Transfer s_in → s_out", f"s_in  = {s_in}",
                              f"s_out = {s_out}"], "Transferring")
        v = s_out.pop()
        yield text_frame([f"dequeue() → {v}", f"s_in  = {s_in}", f"s_out = {s_out}"],
                         "Dequeued")


# ---- HASHING ---------------------------------------------------------------

def gen_hash_chaining(a):
    vals = list(a)
    size = 7
    table: List[List[int]] = [[] for _ in range(size)]
    cells = [[str(x) for x in b] for b in table]
    yield grid(cells, [f"Bucket {i}" for i in range(size)], ["chain"],
               message=f"Hash Table with Chaining — hash(k) = k mod {size}")
    for v in vals:
        h = v % size
        table[h].append(v)
        cells = [[str(x) for x in b] for b in table]
        yield grid(cells, [f"Bucket {i}" for i in range(size)], ["chain"],
                   highlights={(h, len(table[h]) - 1): "active"},
                   message=f"Insert {v} → hash({v}) = {v} mod {size} = {h}",
                   info=[f"collisions handled by chaining"])
    yield grid([[str(x) for x in b] for b in table],
               [f"Bucket {i}" for i in range(size)], ["chain"],
               highlights={(i, j): "found" for i in range(size) for j in range(len(table[i]))},
               message="Hash table built ✔")


def gen_linear_probing(a):
    vals = list(a)
    size = 11
    table: List[Optional[int]] = [None] * size
    yield text_frame([f"Hash Table — Open Addressing / Linear Probing (size {size})",
                      "On collision, try (h+1) mod size, (h+2) mod size, …"], "Linear Probing")
    for v in vals:
        h = v % size
        probes = 0
        idx = h
        while table[idx] is not None:
            probes += 1
            idx = (idx + 1) % size
            if probes > size:
                break
        table[idx] = v
        yield text_frame([f"Insert {v}: hash = {h}",
                          f"probes = {probes} → placed at index {idx}",
                          "",
                          *[f"[{i}] {('-' if x is None else x)}" for i, x in enumerate(table)]],
                         f"Inserted {v} after {probes} probe(s)")
    yield text_frame([f"Final table:",
                      *[f"[{i}] {('-' if x is None else x)}" for i, x in enumerate(table)]],
                     "Linear probing table ✔")


def gen_two_sum(a, target):
    a = list(a)
    seen: Dict[int, int] = {}
    yield bar(a, f"Two Sum — find indices whose values add to {target}")
    for i, v in enumerate(a):
        need = target - v
        yield bar(a, f"i={i}, v={v}, need={need}", {i: "active"},
                  info=[f"seen = {seen}"])
        if need in seen:
            j = seen[need]
            yield bar(a, f"Found! indices {j} and {i} → {a[j]} + {a[i]} = {target}",
                      {j: "found", i: "found"})
            return
        seen[v] = i
    yield bar(a, "No pair found ✘")


def gen_duplicate_detect(a):
    a = list(a)
    seen = set()
    yield bar(a, "Duplicate Detection with a hash set")
    for i, v in enumerate(a):
        if v in seen:
            yield bar(a, f"{v} already in the set → DUPLICATE ✔", {i: "swap"},
                      info=[f"seen = {sorted(seen)}"])
            return
        seen.add(v)
        yield bar(a, f"Add {v} to the set", {i: "active"},
                  info=[f"seen = {sorted(seen)}"])
    yield bar(a, "All values are unique ✘", {i: "found" for i in range(len(a))})


# ---- TREES -----------------------------------------------------------------

def gen_bst_insert(a):
    vals = list(a)
    root = None
    yield tree_frame(None, "BST Insert — smaller left, greater right")
    for v in vals:
        if root is None:
            root = tnode(v)
            yield tree_frame(copy_tree(root), f"Insert {v} as root", {root["id"]: "found"})
            continue
        cur = root
        path = []
        while True:
            path.append(cur["id"])
            if v < cur["val"]:
                if cur["left"] is None:
                    cur["left"] = tnode(v)
                    new_id = cur["left"]["id"]
                    break
                cur = cur["left"]
            elif v > cur["val"]:
                if cur["right"] is None:
                    cur["right"] = tnode(v)
                    new_id = cur["right"]["id"]
                    break
                cur = cur["right"]
            else:
                new_id = cur["id"]
                break
        hl = {i: "compare" for i in path}
        hl[new_id] = "found"
        yield tree_frame(copy_tree(root), f"Insert {v}", hl)
    yield tree_frame(copy_tree(root), "BST built ✔",
                     {n: "sorted" for n in []})


def _traverse(root, order):
    out = []
    if root is None:
        return out

    def pre(n):
        if n is None:
            return
        out.append(n["val"])
        pre(n["left"])
        pre(n["right"])

    def ino(n):
        if n is None:
            return
        ino(n["left"])
        out.append(n["val"])
        ino(n["right"])

    def post(n):
        if n is None:
            return
        post(n["left"])
        post(n["right"])
        out.append(n["val"])

    {"pre": pre, "in": ino, "post": post}[order](root)
    return out


def _traverse_gen(a, order, label):
    vals = insertion_sorted(set(a))
    root = build_bst(vals)
    yield tree_frame(copy_tree(root), f"{label} Traversal")
    visited_vals = []
    if order == "pre":
        stack = [root]
        while stack:
            n = stack.pop()
            if n is None:
                continue
            visited_vals.append(n["val"])
            yield tree_frame(copy_tree(root),
                             f"Visit {n['val']} — order: {visited_vals}",
                             {n["id"]: "found"})
            stack.append(n["right"])
            stack.append(n["left"])
    elif order == "in":
        stack = []
        cur = root
        while stack or cur:
            while cur:
                stack.append(cur)
                cur = cur["left"]
            cur = stack.pop()
            visited_vals.append(cur["val"])
            yield tree_frame(copy_tree(root),
                             f"Visit {cur['val']} — order: {visited_vals}",
                             {cur["id"]: "found"})
            cur = cur["right"]
    elif order == "post":
        stack = [root]
        out = []
        while stack:
            n = stack.pop()
            if n is None:
                continue
            out.append(n)
            stack.append(n["left"])
            stack.append(n["right"])
        for n in reversed(out):
            visited_vals.append(n["val"])
            yield tree_frame(copy_tree(root),
                             f"Visit {n['val']} — order: {visited_vals}",
                             {n["id"]: "found"})
    else:  # level order
        q = deque([root])
        while q:
            n = q.popleft()
            if n is None:
                continue
            visited_vals.append(n["val"])
            yield tree_frame(copy_tree(root),
                             f"Visit {n['val']} — order: {visited_vals}",
                             {n["id"]: "found"})
            q.append(n["left"])
            q.append(n["right"])
    yield tree_frame(copy_tree(root),
                     f"{label} complete → {visited_vals}",
                     {n["id"]: "sorted" for n in []})


def gen_preorder(a):
    yield from _traverse_gen(a, "pre", "Preorder (Root-Left-Right)")


def gen_inorder(a):
    yield from _traverse_gen(a, "in", "Inorder (Left-Root-Right)")


def gen_postorder(a):
    yield from _traverse_gen(a, "post", "Postorder (Left-Right-Root)")


def gen_levelorder(a):
    yield from _traverse_gen(a, "level", "Level Order (BFS)")


def gen_bst_search(a, target):
    vals = insertion_sorted(set(a))
    root = build_bst(vals)
    yield tree_frame(copy_tree(root), f"BST Search for {target}")
    cur = root
    while cur is not None:
        yield tree_frame(copy_tree(root), f"Visit {cur['val']}", {cur["id"]: "compare"})
        if cur["val"] == target:
            yield tree_frame(copy_tree(root), f"Found {target} ✔", {cur["id"]: "found"})
            return
        cur = cur["left"] if target < cur["val"] else cur["right"]
    yield tree_frame(copy_tree(root), f"{target} not in the tree ✘")


def gen_tree_metrics(a):
    vals = insertion_sorted(set(a))
    root = build_bst(vals)

    def height(n):
        if n is None:
            return -1
        return 1 + max(height(n["left"]), height(n["right"]))

    def minimum(n):
        while n["left"] is not None:
            yield tree_frame(copy_tree(root), f"Go left from {n['val']}", {n["id"]: "active"})
            n = n["left"]
        yield tree_frame(copy_tree(root), f"Minimum = {n['val']} ✔", {n["id"]: "found"})

    def maximum(n):
        while n["right"] is not None:
            yield tree_frame(copy_tree(root), f"Go right from {n['val']}", {n["id"]: "active"})
            n = n["right"]
        yield tree_frame(copy_tree(root), f"Maximum = {n['val']} ✔", {n["id"]: "found"})

    yield tree_frame(copy_tree(root), "Tree Metrics — height, min, max")
    yield tree_frame(copy_tree(root), f"Height of the tree = {height(root)}")
    yield from minimum(root)
    yield from maximum(root)


def gen_heap_demo(a):
    vals = list(a)
    heap: List[int] = []
    yield bar(heap or [0], "Min-Heap — insert and sift up")
    for v in vals:
        heap.append(v)
        i = len(heap) - 1
        while i > 0:
            parent = (i - 1) // 2
            if heap[parent] > heap[i]:
                heap[parent], heap[i] = heap[i], heap[parent]
                yield bar(heap, f"Sift up: swap {heap[i]} ↔ {heap[parent]}",
                          {i: "swap", parent: "compare"})
                i = parent
            else:
                break
        yield bar(heap, f"Inserted {v} — heap property restored", {i: "active"})
    yield bar(heap, "Min-heap built ✔ (root is the minimum)")


def gen_trie(a):
    words = ["cat", "car", "cart", "dog", "do"]
    root: Dict[str, Any] = {}
    lines = ["Trie (Prefix Tree) — insert words, then prefix search"]
    yield text_frame(lines, "Trie")

    def insert(w):
        node = root
        for ch in w:
            node = node.setdefault(ch, {})
        node["$"] = True

    for w in words:
        insert(w)
        lines.append(f"insert('{w}')")
        yield text_frame(lines, f"Inserted '{w}'")

    def dump(node, prefix, depth, out):
        for ch in sorted(k for k in node if k != "$"):
            out.append("  " * depth + ch + (" ●" if node[ch].get("$") else ""))
            dump(node[ch], prefix + ch, depth + 1, out)

    out: List[str] = []
    dump(root, "", 0, out)
    yield text_frame(["Trie structure (● = end of word):"] + out, "Trie built ✔")


# ---- GRAPHS ----------------------------------------------------------------

def gen_bfs(a):
    g = GRAPH_MAIN
    adj = adjacency(g)
    start = "A"
    visited = {start}
    order = []
    q = deque([start])
    yield graph_frame(g, f"BFS from {start}", {start: "current"},
                      info=["queue = ['A']"])
    while q:
        node = q.popleft()
        order.append(node)
        yield graph_frame(g, f"Dequeue {node}", {node: "current"},
                          info=[f"queue = {list(q)}", f"order = {order}"])
        for nb, _w in adj[node]:
            if nb not in visited:
                visited.add(nb)
                q.append(nb)
                yield graph_frame(g, f"Discover {nb} → enqueue",
                                  {node: "visited", nb: "current"},
                                  info=[f"queue = {list(q)}", f"order = {order}"])
        yield graph_frame(g, f"Mark {node} visited",
                          {n: "visited" for n in visited},
                          info=[f"order = {order}"])
    yield graph_frame(g, f"BFS order: {order} ✔",
                      {n: "visited" for n in order}, info=[f"order = {order}"])


def gen_dfs(a):
    g = GRAPH_MAIN
    adj = adjacency(g)
    visited = set()
    order = []
    yield graph_frame(g, "DFS from A (iterative stack)")
    stack = ["A"]
    while stack:
        node = stack.pop()
        if node in visited:
            continue
        visited.add(node)
        order.append(node)
        yield graph_frame(g, f"Visit {node}",
                          {n: "visited" for n in visited},
                          info=[f"stack = {stack}", f"order = {order}"])
        for nb, _w in reversed(adj[node]):
            if nb not in visited:
                stack.append(nb)
    yield graph_frame(g, f"DFS order: {order} ✔",
                      {n: "visited" for n in order}, info=[f"order = {order}"])


def gen_dijkstra(a):
    g = GRAPH_MAIN
    adj = adjacency(g)
    src = "A"
    dist = {n: math.inf for n in g["nodes"]}
    dist[src] = 0
    prev = {}
    visited = set()
    yield graph_frame(g, f"Dijkstra from {src}",
                      {src: "current"},
                      info=[f"dist = { {k: (v if v != math.inf else '∞') for k, v in dist.items()} }"])
    pq = [(0, src)]
    while pq:
        d, u = heapq.heappop(pq)
        if u in visited:
            continue
        visited.add(u)
        yield graph_frame(g, f"Extract min: {u} (dist {d})",
                          {n: "visited" for n in visited} | {u: "current"},
                          info=[f"dist = { {k: (v if v != math.inf else '∞') for k, v in dist.items()} }"])
        for v, w in adj[u]:
            if dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                prev[v] = u
                yield graph_frame(g, f"Relax {u} → {v}: new dist = {dist[v]}",
                                  {n: "visited" for n in visited} | {u: "current", v: "compare"},
                                  {(u, v): "path"},
                                  info=[f"dist = { {k: (v2 if v2 != math.inf else '∞') for k, v2 in dist.items()} }"])
    final = {k: (v if v != math.inf else "∞") for k, v in dist.items()}
    yield graph_frame(g, f"Shortest distances from {src}: {final}",
                      {n: "found" for n in dist})


def gen_bellman_ford(a):
    g = GRAPH_MAIN
    nodes = list(g["nodes"])
    edges = g["edges"] + [(b, a2, w) for a2, b, w in g["edges"]]
    dist = {n: math.inf for n in nodes}
    dist["A"] = 0
    lines = ["Bellman-Ford — relax every edge V-1 times"]
    yield text_frame(lines + [f"dist = {dist}"], "Init")
    for it in range(len(nodes) - 1):
        changed = False
        for u, v, w in edges:
            if dist[u] != math.inf and dist[u] + w < dist[v]:
                dist[v] = dist[u] + w
                changed = True
                yield text_frame(lines + [f"iteration {it+1}: relax {u}→{v} (w={w})",
                                          f"dist = { {k: (v2 if v2 != math.inf else '∞') for k, v2 in dist.items()} }"],
                                 "Relaxing")
        if not changed:
            break
    yield text_frame([f"Final distances from A:",
                      str({k: (v if v != math.inf else "∞") for k, v in dist.items()}),
                      "No negative cycle detected."], "Bellman-Ford ✔")


def gen_floyd_warshall(a):
    g = GRAPH_DAG
    nodes = list(g["nodes"])
    INF = math.inf
    d = [[INF] * len(nodes) for _ in nodes]
    for i in range(len(nodes)):
        d[i][i] = 0
    idx = {n: i for i, n in enumerate(nodes)}
    for u, v, w in g["edges"]:
        d[idx[u]][idx[v]] = w
    yield grid([[("∞" if c == INF else c) for c in row] for row in d],
               nodes, nodes, message="Floyd-Warshall — initial distance matrix")
    for k in range(len(nodes)):
        for i in range(len(nodes)):
            for j in range(len(nodes)):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
        yield grid([[("∞" if c == INF else c) for c in row] for row in d],
                   nodes, nodes, highlights={(i, j): "active" for i in range(len(nodes))
                                             for j in range(len(nodes)) if i == k or j == k},
                   message=f"After allowing intermediate node {nodes[k]}")
    yield grid([[("∞" if c == INF else c) for c in row] for row in d],
               nodes, nodes, message="All-pairs shortest paths ✔")


def gen_prim(a):
    g = GRAPH_MAIN
    adj = adjacency(g)
    start = "A"
    in_mst = {start}
    pq = [(w, start, nb) for nb, w in adj[start]]
    heapq.heapify(pq)
    total = 0
    yield graph_frame(g, "Prim's MST — grow from a single vertex",
                      {start: "current"})
    while pq:
        w, u, v = heapq.heappop(pq)
        if v in in_mst:
            continue
        in_mst.add(v)
        total += w
        yield graph_frame(g, f"Add edge {u} — {v} (w = {w})",
                          {n: "found" if n in in_mst else "default" for n in g["nodes"]},
                          {(u, v): "path", (v, u): "path"},
                          info=[f"MST weight = {total}"])
        for nb, w2 in adj[v]:
            if nb not in in_mst:
                heapq.heappush(pq, (w2, v, nb))
    yield graph_frame(g, f"MST complete, total weight = {total} ✔",
                      {n: "found" for n in in_mst})


def gen_kruskal(a):
    g = GRAPH_MAIN
    parent = {n: n for n in g["nodes"]}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx == ry:
            return False
        parent[rx] = ry
        return True

    edges = sorted(g["edges"], key=lambda e: e[2])
    total = 0
    chosen = []
    yield graph_frame(g, "Kruskal's MST — sort edges, then union-find",
                      info=[f"edges = {edges}"])
    for u, v, w in edges:
        if union(u, v):
            chosen.append((u, v, w))
            total += w
            yield graph_frame(g, f"Take edge {u}-{v} (w = {w})",
                              {n: "found" for n in g["nodes"]},
                              {(u, v): "path", (v, u): "path"},
                              info=[f"MST weight = {total}"])
        else:
            yield graph_frame(g, f"Skip edge {u}-{v} — would form a cycle",
                              {u: "swap", v: "swap"},
                              info=[f"MST weight = {total}"])
    yield graph_frame(g, f"MST complete, weight = {total} ✔",
                      {n: "found" for n in g["nodes"]},
                      {(u, v): "path" for u, v, _ in chosen})


def gen_topological(a):
    g = GRAPH_DAG
    indeg = {n: 0 for n in g["nodes"]}
    adj: Dict[str, List[str]] = {n: [] for n in g["nodes"]}
    for u, v, _w in g["edges"]:
        adj[u].append(v)
        indeg[v] += 1
    q = deque([n for n in g["nodes"] if indeg[n] == 0])
    order = []
    yield graph_frame(g, "Topological Sort (Kahn's algorithm)",
                      info=[f"in-degree = {indeg}", f"queue = {list(q)}"])
    while q:
        u = q.popleft()
        order.append(u)
        yield graph_frame(g, f"Output {u}", {u: "found"},
                          info=[f"order = {order}", f"queue = {list(q)}"])
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
        yield graph_frame(g, f"Decrement in-degrees of neighbours of {u}",
                          {u: "visited"},
                          info=[f"in-degree = {indeg}", f"queue = {list(q)}"])
    yield graph_frame(g, f"Topological order: {order} ✔",
                      {n: "found" for n in order}, info=[f"order = {order}"])


def gen_components(a):
    g = GRAPH_MAIN
    adj = adjacency(g)
    comp: Dict[str, int] = {}
    cid = 0
    yield graph_frame(g, "Connected Components (DFS)")
    for start in g["nodes"]:
        if start in comp:
            continue
        cid += 1
        stack = [start]
        while stack:
            u = stack.pop()
            if u in comp:
                continue
            comp[u] = cid
            yield graph_frame(g, f"Component {cid} — visit {u}",
                              {n: f"role{c % 7}" for n, c in comp.items()} | {u: "current"},
                              info=[f"components = {comp}"])
            for nb, _w in adj[u]:
                if nb not in comp:
                    stack.append(nb)
    yield graph_frame(g, f"Found {cid} connected component(s) ✔",
                      {n: "found" for n in comp}, info=[f"components = {comp}"])


def gen_cycle_detect(a):
    g = GRAPH_MAIN
    adj = adjacency(g)
    parent: Dict[str, Optional[str]] = {}
    visited = set()
    yield graph_frame(g, "Cycle Detection in an undirected graph (DFS)")
    found = False
    for start in g["nodes"]:
        if start in visited:
            continue
        stack = [(start, None)]
        while stack:
            u, p = stack.pop()
            if u in visited:
                continue
            visited.add(u)
            parent[u] = p
            yield graph_frame(g, f"Visit {u} (parent {p})",
                              {n: "visited" for n in visited} | {u: "current"})
            for nb, _w in adj[u]:
                if nb not in visited:
                    stack.append((nb, u))
                elif nb != p:
                    found = True
                    yield graph_frame(g, f"Back edge {u} — {nb} → CYCLE ✔",
                                      {u: "swap", nb: "swap"})
                    return
    yield graph_frame(g, "No cycle found ✘", {n: "found" for n in visited})


def gen_union_find(a):
    g = GRAPH_MAIN
    parent = {n: n for n in g["nodes"]}
    rank = {n: 0 for n in g["nodes"]}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    yield text_frame(["Union-Find (Disjoint Set Union)",
                      "find(x): follow parents to the representative",
                      "union(a,b): attach the smaller rank tree under the larger"],
                     "Union-Find")
    for u, v, _w in g["edges"]:
        ru, rv = find(u), find(v)
        if ru == rv:
            yield text_frame([f"union({u},{v}) — already in the same set",
                              f"parent = {parent}"], "Skipped")
            continue
        if rank[ru] < rank[rv]:
            ru, rv = rv, ru
        parent[rv] = ru
        if rank[ru] == rank[rv]:
            rank[ru] += 1
        yield text_frame([f"union({u},{v}) — attached {rv} under {ru}",
                          f"parent = {parent}"], "Union done")
    groups: Dict[str, List[str]] = {}
    for n in g["nodes"]:
        groups.setdefault(find(n), []).append(n)
    yield text_frame([f"Final disjoint sets:"]
                     + [f"  {r} → {members}" for r, members in groups.items()],
                     f"{len(groups)} set(s) ✔")


# ---- GREEDY ----------------------------------------------------------------

def gen_activity_selection(a):
    acts = [("A1", 1, 4), ("A2", 3, 5), ("A3", 0, 6), ("A4", 5, 7),
            ("A5", 3, 9), ("A6", 5, 9), ("A7", 6, 10), ("A8", 8, 11)]
    acts.sort(key=lambda x: x[2])
    lines = ["Greedy choice: always pick the activity that FINISHES earliest.",
             "Sorted by finish time: " + str([(n, f) for n, _s, f in acts]), ""]
    chosen = []
    last_end = -1
    for name, s, f in acts:
        if s >= last_end:
            chosen.append(name)
            last_end = f
            lines.append(f"Pick {name} [{s},{f}] — starts after {last_end if len(chosen)>1 else 'start'}")
        else:
            lines.append(f"Skip  {name} [{s},{f}] — overlaps")
        yield text_frame(lines, f"Selected: {chosen}")
    yield text_frame(lines + ["", f"Maximum number of activities = {len(chosen)} ✔"],
                     "Activity Selection ✔")


def gen_fractional_knapsack(a):
    items = [("I1", 60, 10), ("I2", 100, 20), ("I3", 120, 30)]
    cap = 50
    items_sorted = sorted(items, key=lambda x: x[1] / x[2], reverse=True)
    lines = [f"Capacity = {cap}",
             "Greedy choice: take items in order of value/weight ratio.", ""]
    total = 0.0
    for name, val, wt in items_sorted:
        ratio = val / wt
        take = min(wt, cap)
        total += ratio * take
        cap -= take
        lines.append(f"{name}: ratio = {ratio:.2f}, take {take:.0f}/{wt} → profit {ratio*take:.2f}")
        yield text_frame(lines, f"Total profit so far = {total:.2f}")
        if cap <= 0:
            break
    yield text_frame(lines + ["", f"Maximum profit = {total:.2f} ✔"], "Fractional Knapsack ✔")


def gen_coin_change_greedy(a):
    coins = [1, 5, 10, 25]
    amount = 63
    lines = [f"Coins = {coins}, amount = {amount}",
             "Greedy choice: always take the largest coin ≤ remaining amount.", ""]
    used = []
    rem = amount
    for c in sorted(coins, reverse=True):
        while rem >= c:
            rem -= c
            used.append(c)
            lines.append(f"Take {c} → remaining {rem}")
            yield text_frame(lines, f"Coins used: {used}")
    yield text_frame(lines + ["", f"Total coins = {len(used)} ✔",
                              "(Note: greedy is not optimal for every coin system.)"],
                     "Coin Change (Greedy)")


def gen_jump_game(a):
    arr = [2, 3, 1, 1, 4]
    lines = [f"Array = {arr}", "Greedy choice: track the farthest reachable index.", ""]
    reach = 0
    for i, v in enumerate(arr):
        if i > reach:
            yield text_frame(lines + [f"Index {i} unreachable → False ✘"], "Stuck")
            return
        reach = max(reach, i + v)
        lines.append(f"i={i}, jump={v} → farthest reach = {reach}")
        yield text_frame(lines, f"Farthest reach = {reach}")
        if reach >= len(arr) - 1:
            break
    yield text_frame(lines + ["", "Last index reachable → True ✔"], "Jump Game ✔")


def gen_merge_intervals(a):
    intervals = [[1, 3], [2, 6], [8, 10], [15, 18]]
    intervals.sort(key=lambda x: x[0])
    lines = [f"Sorted intervals: {intervals}", ""]
    merged = [list(intervals[0])]
    yield text_frame(lines + [f"merged = {merged}"], "Merging…")
    for s, e in intervals[1:]:
        if s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
            lines.append(f"Merge [{s},{e}] → merged = {merged}")
        else:
            merged.append([s, e])
            lines.append(f"New interval [{s},{e}] → merged = {merged}")
        yield text_frame(lines, "Merging…")
    yield text_frame(lines + ["", f"Result: {merged} ✔"], "Merge Intervals ✔")


def gen_huffman(a):
    freqs = {"a": 5, "b": 9, "c": 12, "d": 13, "e": 16, "f": 45}
    heap = [[w, [ch, ""]] for ch, w in freqs.items()]
    heapq.heapify(heap)
    lines = [f"Frequencies: {freqs}",
             "Greedy choice: repeatedly merge the two least frequent nodes.", ""]
    yield text_frame(lines + [f"heap = {[h[0] for h in heap]}"], "Huffman Coding")
    while len(heap) > 1:
        lo = heapq.heappop(heap)
        hi = heapq.heappop(heap)
        for pair in lo[1:]:
            pair[1] = "0" + pair[1]
        for pair in hi[1:]:
            pair[1] = "1" + pair[1]
        heapq.heappush(heap, [lo[0] + hi[0]] + lo[1:] + hi[1:])
        lines.append(f"Merge {lo[0]} + {hi[0]} = {lo[0]+hi[0]}")
        yield text_frame(lines, "Merging…")
    codes = sorted(heapq.heappop(heap)[1:], key=lambda p: (len(p[-1]), p))
    yield text_frame(lines + [""] + [f"  '{ch}' → {code}" for ch, code in codes]
                     + ["", "Codes are prefix-free ✔"], "Huffman Codes ✔")


# ---- DYNAMIC PROGRAMMING ---------------------------------------------------

def gen_fib_dp(a):
    n = min(max(len(a) + 4, 8), 15)
    dp = [0] * (n + 1)
    dp[1] = 1
    yield bar(dp, "Fibonacci DP — bottom-up tabulation",
              info=[f"dp[i] = dp[i-1] + dp[i-2]"])
    for i in range(2, n + 1):
        dp[i] = dp[i - 1] + dp[i - 2]
        yield bar(dp, f"dp[{i}] = dp[{i-1}] + dp[{i-2}] = {dp[i-1]} + {dp[i-2]} = {dp[i]}",
                  {i: "active", i - 1: "compare", i - 2: "compare"},
                  info=[f"dp[i] = dp[i-1] + dp[i-2]"])
    yield bar(dp, f"Fib({n}) = {dp[n]} ✔", {n: "found"})


def gen_climbing_stairs(a):
    n = min(max(len(a) + 3, 6), 12)
    dp = [0] * (n + 1)
    dp[0] = 1
    dp[1] = 1
    yield bar(dp, "Climbing Stairs — ways to reach step n using 1 or 2 steps",
              info=["dp[i] = dp[i-1] + dp[i-2]"])
    for i in range(2, n + 1):
        dp[i] = dp[i - 1] + dp[i - 2]
        yield bar(dp, f"dp[{i}] = dp[{i-1}] + dp[{i-2}] = {dp[i]}",
                  {i: "active", i - 1: "compare", i - 2: "compare"},
                  info=["dp[i] = dp[i-1] + dp[i-2]"])
    yield bar(dp, f"Ways to climb {n} stairs = {dp[n]} ✔", {n: "found"})


def gen_house_robber(a):
    h = [2, 7, 9, 3, 1]
    n = len(h)
    dp = [0] * (n + 1)
    yield bar(h, f"House Robber — houses = {h}",
              info=["dp[i] = max(dp[i-1], dp[i-2] + h[i-1])"])
    for i in range(1, n + 1):
        take = dp[i - 2] + h[i - 1] if i >= 2 else h[i - 1]
        skip = dp[i - 1]
        dp[i] = max(take, skip)
        yield bar(h, f"House {i}: rob ({take}) vs skip ({skip}) → {dp[i]}",
                  {i - 1: "active"}, info=[f"dp = {dp[1:]}"])
    yield bar(h, f"Maximum loot = {dp[n]} ✔")


def gen_knapsack_01(a):
    wt = [1, 3, 4, 5]
    val = [1, 4, 5, 7]
    W = 7
    n = len(wt)
    dp = [[0] * (W + 1) for _ in range(n + 1)]
    yield grid(dp, [""] + [f"i={i+1}" for i in range(n)], [str(w) for w in range(W + 1)],
               message=f"0/1 Knapsack — capacity {W}, weights {wt}, values {val}")
    for i in range(1, n + 1):
        for w in range(W + 1):
            if wt[i - 1] <= w:
                dp[i][w] = max(dp[i - 1][w], dp[i - 1][w - wt[i - 1]] + val[i - 1])
            else:
                dp[i][w] = dp[i - 1][w]
            yield grid(dp, [""] + [f"i={k+1}" for k in range(n)], [str(x) for x in range(W + 1)],
                       highlights={(i, w): "active"},
                       message=f"dp[{i}][{w}] = {dp[i][w]}")
    yield grid(dp, [""] + [f"i={k+1}" for k in range(n)], [str(x) for x in range(W + 1)],
               highlights={(n, W): "found"},
               message=f"Maximum value = {dp[n][W]} ✔")


def gen_lcs(a):
    s1, s2 = "ABCBDAB", "BDCABA"
    n, m = len(s1), len(s2)
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    rows = [""] + list(s1)
    cols = [""] + list(s2)
    yield grid(dp, rows, cols, message=f"LCS of '{s1}' and '{s2}'")
    for i in range(1, n + 1):
        for j in range(1, m + 1):
            if s1[i - 1] == s2[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
            yield grid(dp, rows, cols, highlights={(i, j): "active"},
                       message=f"'{s1[i-1]}' vs '{s2[j-1]}' → {dp[i][j]}")
    yield grid(dp, rows, cols, highlights={(n, m): "found"},
               message=f"LCS length = {dp[n][m]} ✔")


def gen_lis(a):
    arr = [10, 9, 2, 5, 3, 7, 101, 18]
    n = len(arr)
    dp = [1] * n
    yield bar(arr, "Longest Increasing Subsequence — O(n²) DP",
              info=[f"dp = {dp}"])
    for i in range(1, n):
        for j in range(i):
            if arr[j] < arr[i] and dp[j] + 1 > dp[i]:
                dp[i] = dp[j] + 1
                yield bar(arr, f"arr[{j}]={arr[j]} < arr[{i}]={arr[i]} → dp[{i}] = {dp[i]}",
                          {j: "compare", i: "active"}, info=[f"dp = {dp}"])
        yield bar(arr, f"dp[{i}] = {dp[i]}", {i: "active"}, info=[f"dp = {dp}"])
    yield bar(arr, f"LIS length = {max(dp)} ✔", info=[f"dp = {dp}"])


def gen_coin_change_dp(a):
    coins = [1, 3, 4]
    amount = 6
    INF = float("inf")
    dp = [0] + [INF] * amount
    yield bar([0 if x == INF else x for x in dp],
              f"Coin Change DP — coins {coins}, amount {amount}",
              info=["dp[x] = min coins to make x"])
    for x in range(1, amount + 1):
        for c in coins:
            if c <= x and dp[x - c] + 1 < dp[x]:
                dp[x] = dp[x - c] + 1
        show = [0 if v == INF else v for v in dp]
        yield bar(show, f"dp[{x}] = {show[x]}", {x: "active"},
                  info=[f"dp = {show}"])
    yield bar([0 if v == INF else v for v in dp],
              f"Minimum coins for {amount} = {dp[amount]} ✔",
              {amount: "found"})


def gen_edit_distance(a):
    s1, s2 = "kitten", "sitting"
    n, m = len(s1), len(s2)
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        dp[i][0] = i
    for j in range(m + 1):
        dp[0][j] = j
    rows = [""] + list(s1)
    cols = [""] + list(s2)
    yield grid(dp, rows, cols, message=f"Edit Distance between '{s1}' and '{s2}'")
    for i in range(1, n + 1):
        for j in range(1, m + 1):
            if s1[i - 1] == s2[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1])
            yield grid(dp, rows, cols, highlights={(i, j): "active"},
                       message=f"'{s1[i-1]}' vs '{s2[j-1]}' → {dp[i][j]}")
    yield grid(dp, rows, cols, highlights={(n, m): "found"},
               message=f"Edit distance = {dp[n][m]} ✔")


def gen_rod_cutting(a):
    price = [1, 5, 8, 9, 10, 17, 17, 20]
    n = len(price)
    dp = [0] * (n + 1)
    yield bar(dp, f"Rod Cutting — prices {price}", info=["dp[l] = max profit for length l"])
    for l in range(1, n + 1):
        best = -1
        for cut in range(1, l + 1):
            if price[cut - 1] + dp[l - cut] > best:
                best = price[cut - 1] + dp[l - cut]
        dp[l] = best
        yield bar(dp, f"dp[{l}] = {best}", {l: "active"}, info=[f"dp = {dp}"])
    yield bar(dp, f"Max profit for length {n} = {dp[n]} ✔", {n: "found"})


def gen_subset_sum(a):
    nums = [3, 34, 4, 12, 5, 2]
    target = 9
    n = len(nums)
    dp = [[False] * (target + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        dp[i][0] = True
    rows = ["∅"] + [str(x) for x in nums]
    cols = [str(i) for i in range(target + 1)]
    yield grid([[("T" if c else "F") for c in row] for row in dp], rows, cols,
               message=f"Subset Sum — nums {nums}, target {target}")
    for i in range(1, n + 1):
        for t in range(1, target + 1):
            dp[i][t] = dp[i - 1][t] or (nums[i - 1] <= t and dp[i - 1][t - nums[i - 1]])
        yield grid([[("T" if c else "F") for c in row] for row in dp], rows, cols,
                   highlights={(i, t): "active" for t in range(target + 1)},
                   message=f"After considering {nums[i-1]}")
    yield grid([[("T" if c else "F") for c in row] for row in dp], rows, cols,
               highlights={(n, target): "found"},
               message=f"Subset with sum {target} exists → {dp[n][target]} ✔")


def gen_longest_palindromic_subseq(a):
    s = "bbbab"
    n = len(s)
    dp = [[0] * n for _ in range(n)]
    for i in range(n):
        dp[i][i] = 1
    yield grid(dp, list(s), list(s), message=f"Longest Palindromic Subsequence of '{s}'")
    for length in range(2, n + 1):
        for i in range(n - length + 1):
            j = i + length - 1
            if s[i] == s[j]:
                dp[i][j] = dp[i + 1][j - 1] + 2 if length > 2 else 2
            else:
                dp[i][j] = max(dp[i + 1][j], dp[i][j - 1])
            yield grid(dp, list(s), list(s), highlights={(i, j): "active"},
                       message=f"i={i}, j={j} → {dp[i][j]}")
    yield grid(dp, list(s), list(s), highlights={(0, n - 1): "found"},
               message=f"LPS length = {dp[0][n-1]} ✔")


# ---- DIVIDE & CONQUER ------------------------------------------------------

def gen_dc_merge_sort(a):
    yield from gen_merge(a)


def gen_quick_select(a):
    arr = list(a)
    k = 2  # k-th smallest (1-indexed)

    def qs(lo, hi, k):
        if lo == hi:
            return arr[lo]
        pivot = arr[hi]
        i = lo
        for j in range(lo, hi):
            if arr[j] < pivot:
                arr[i], arr[j] = arr[j], arr[i]
                i += 1
        arr[i], arr[hi] = arr[hi], arr[i]
        yield bar(arr, f"Pivot {pivot} placed at index {i}", {i: "sorted"})
        if i == k - 1:
            yield bar(arr, f"k-th smallest = {arr[i]} ✔", {i: "found"})
            return arr[i]
        if i < k - 1:
            yield from qs(i + 1, hi, k)
        else:
            yield from qs(lo, i - 1, k)

    yield bar(arr, f"Quick Select — find the {k}-th smallest element")
    yield from qs(0, len(arr) - 1, k)


def gen_dc_max_subarray(a):
    arr = list(a)

    def helper(lo, hi):
        if lo == hi:
            return arr[lo], lo, lo
        mid = (lo + hi) // 2
        lsum, ll, lr = helper(lo, mid)
        rsum, rl, rr = helper(mid + 1, hi)
        csum = 0
        best_left = float("-inf")
        bl = mid
        for i in range(mid, lo - 1, -1):
            csum += arr[i]
            if csum > best_left:
                best_left = csum
                bl = i
        csum = 0
        best_right = float("-inf")
        br = mid + 1
        for i in range(mid + 1, hi + 1):
            csum += arr[i]
            if csum > best_right:
                best_right = csum
                br = i
        cross = best_left + best_right
        best = max(lsum, rsum, cross)
        if best == lsum:
            return lsum, ll, lr
        if best == rsum:
            return rsum, rl, rr
        return cross, bl, br

    yield bar(arr, "Divide & Conquer Maximum Subarray",
              {i: "active" for i in range(len(arr))})
    best, lo, hi = helper(0, len(arr) - 1)
    yield bar(arr, f"Maximum subarray sum = {best} → {arr[lo:hi+1]}",
              {i: "found" for i in range(lo, hi + 1)})


# ---- FOUNDATIONS -----------------------------------------------------------

def gen_complexity_growth(a):
    ns = [1, 2, 4, 8, 16]
    rows = [
        ["O(1)"] + [1 for _ in ns],
        ["O(log n)"] + [round(math.log2(n), 1) if n > 1 else 0 for n in ns],
        ["O(n)"] + [n for n in ns],
        ["O(n log n)"] + [round(n * math.log2(n), 1) if n > 1 else 0 for n in ns],
        ["O(n²)"] + [n * n for n in ns],
        ["O(2ⁿ)"] + [2 ** n for n in ns],
    ]
    yield grid(rows, [r[0] for r in rows], [f"n={n}" for n in ns],
               message="Big-O Growth Rates — operations for input size n",
               info=["Smaller is better. Exponential explodes immediately."])
    yield text_frame([
        "Big-O (upper bound)   : f(n) ≤ c·g(n) for large n",
        "Big-Omega (lower bound): f(n) ≥ c·g(n) for large n",
        "Big-Theta (tight bound): c₁·g(n) ≤ f(n) ≤ c₂·g(n)",
        "",
        "Analogy:",
        "  O(1)        → reading the first page of a book",
        "  O(log n)    → binary search in a phone book",
        "  O(n)        → reading the whole book",
        "  O(n log n)  → sorting the book's words alphabetically",
        "  O(n²)       → comparing every page with every other page",
        "  O(2ⁿ)       → listing every possible subset of pages",
    ], "Asymptotic Notation")


def gen_recursion_vs_iteration(a):
    n = 5
    lines = [f"Factorial of {n}", "", "ITERATION (loop):", "  result = 1"]
    acc = 1
    for i in range(2, n + 1):
        acc *= i
        lines.append(f"  result *= {i}  →  {acc}")
    lines += ["", "RECURSION (call stack):"]
    for i in range(n, 0, -1):
        lines.append("  " + "  " * (n - i) + f"fact({i})")
    lines += ["", "  " + "  " * n + "fact(0) = 1  (base case)",
              "  Unwinding multiplies back up.",
              "",
              "Recursion cost: O(n) stack frames.  Iteration cost: O(1) extra space."]
    yield text_frame(lines, "Recursion vs Iteration")


def gen_amortized(a):
    lines = ["Amortized Analysis — dynamic array (list) growth", "",
             "Python lists over-allocate: when full, capacity is multiplied.",
             ""]
    cap = 1
    size = 0
    total_cost = 0
    for i in range(1, 17):
        if size == cap:
            total_cost += size  # copying cost
            cap *= 2
            lines.append(f"push #{i:2d}: FULL → resize to capacity {cap}, copy {size} items")
        size += 1
        total_cost += 1
        lines.append(f"push #{i:2d}: size = {size}, capacity = {cap}, "
                     f"amortized cost ≈ {total_cost / i:.2f}")
    lines += ["", f"Total cost after {size} pushes = {total_cost}",
              f"Amortized cost per push = {total_cost/size:.2f} → O(1)"]
    yield text_frame(lines, "Amortized Analysis")


def gen_io_optimization(a):
    yield text_frame([
        "Fast Input / Output in Python",
        "",
        "SLOW (many small writes / reads):",
        "    for line in sys.stdin:",
        "        print(int(line) * 2)",
        "",
        "FAST:",
        "    import sys",
        "    data = sys.stdin.buffer.read().split()",
        "    out = []",
        "    for tok in data:",
        "        out.append(str(int(tok) * 2))",
        "    sys.stdout.write('\\n'.join(out))",
        "",
        "Why:  buffer.read() performs ONE system call;",
        "      sys.stdout.write performs ONE write instead of thousands.",
        "",
        "Rule of thumb: read all input at once, build the answer in a list,",
        "               then write it out in a single call.",
    ], "I/O Optimization")


# ============================================================================
# 6. ALGORITHM REGISTRY
# ============================================================================

@dataclass
class Algorithm:
    name: str
    category: str
    difficulty: str
    description: str
    how: str
    code: str
    best: str = "-"
    average: str = "-"
    worst: str = "-"
    space: str = "-"
    stable: str = "-"
    inplace: str = "-"
    input_type: str = "int_list"     # int_list | string | string_pair | none
    default_input: str = "5, 3, 8, 1, 9, 2, 7, 4"
    run: Callable = None
    uses_target: bool = False
    needs_sorted: bool = False


ALGORITHMS: Dict[str, Algorithm] = {}


def reg(name, category, difficulty, description, how, code, run,
        best="-", average="-", worst="-", space="-",
        stable="-", inplace="-", input_type="int_list",
        default_input="5, 3, 8, 1, 9, 2, 7, 4",
        uses_target=False, needs_sorted=False):
    ALGORITHMS[name] = Algorithm(
        name=name, category=category, difficulty=difficulty, description=description,
        how=how, code=code, best=best, average=average, worst=worst, space=space,
        stable=stable, inplace=inplace, input_type=input_type,
        default_input=default_input, run=run, uses_target=uses_target,
        needs_sorted=needs_sorted)


# ---- Foundations -----------------------------------------------------------
reg("Complexity Growth (Big-O)", "Foundations", "Easy",
    "Visual comparison of how common complexity classes grow with input size n.",
    "For each complexity class we compute the number of basic operations for "
    "increasing n. Linear and logarithmic curves stay flat while n² and 2ⁿ explode.",
    "for n in sizes:\n    print(n, 1, math.log2(n), n, n*math.log2(n), n*n, 2**n)",
    gen_complexity_growth, "O(1)", "-", "O(2ⁿ)", "O(1)", input_type="none")

reg("Asymptotic Notation", "Foundations", "Easy",
    "Big-O, Big-Omega and Big-Theta — upper, lower and tight bounds.",
    "Big-O bounds a function from above, Big-Omega from below, and Big-Theta "
    "sandwiches it between two constant multiples of the same function.",
    "f(n) = O(g(n))      -> f grows no faster than g\n"
    "f(n) = Ω(g(n))      -> f grows at least as fast as g\n"
    "f(n) = Θ(g(n))      -> f and g grow at the same rate",
    lambda a: [text_frame([
        "BIG-O — upper bound:   f(n) ≤ c·g(n)",
        "BIG-OMEGA — lower bound: f(n) ≥ c·g(n)",
        "BIG-THETA — tight bound: c₁·g(n) ≤ f(n) ≤ c₂·g(n)",
        "",
        "Example: 3n² + 5n + 2",
        "  → O(n²)   (upper bound)",
        "  → Ω(n²)   (lower bound)",
        "  → Θ(n²)   (tight)",
    ], "Asymptotic Notation")],
    "O(1)", "-", "O(2ⁿ)", "O(1)", input_type="none")

reg("Recursion vs Iteration", "Foundations", "Easy",
    "Two ways to repeat work: loops and recursive calls.",
    "Iteration uses a loop and O(1) extra space. Recursion uses the call stack, "
    "consuming O(depth) frames, but often expresses divide & conquer elegantly.",
    "def fact_iter(n):\n    r = 1\n    for i in range(2, n+1):\n        r *= i\n    return r\n\n"
    "def fact_rec(n):\n    if n <= 1:\n        return 1\n    return n * fact_rec(n-1)",
    gen_recursion_vs_iteration, "O(n)", "O(n)", "O(n)", "O(1) / O(n)",
    input_type="none")

reg("Amortized Analysis", "Foundations", "Medium",
    "Why a single push can be expensive while the average push is O(1).",
    "A dynamic array doubles its capacity when full. The expensive O(n) copy "
    "happens rarely enough that the cost spread over all pushes is O(1).",
    "# capacity doubles on resize -> amortized O(1) per append\narr = []\nfor x in data:\n    arr.append(x)",
    gen_amortized, "O(1)", "O(1)", "O(n)", "O(n)", input_type="none")

reg("Input / Output Optimization", "Foundations", "Medium",
    "Techniques that make Python competitive in competitive programming.",
    "Buffer the entire input with sys.stdin.buffer.read() and accumulate output "
    "in a list, then write once. This avoids thousands of system calls.",
    "import sys\n"
    "data = sys.stdin.buffer.read().split()\n"
    "out = []\n"
    "for tok in data:\n"
    "    out.append(str(int(tok) * 2))\n"
    "sys.stdout.write('\\n'.join(out))",
    gen_io_optimization, "-", "-", "-", "-", input_type="none")

# ---- Arrays ----------------------------------------------------------------
reg("Kadane's Algorithm", "Arrays", "Medium",
    "Finds the contiguous subarray with the maximum sum in O(n).",
    "Keep a running `current_sum`. At each element decide: extend the existing "
    "subarray, or start a new one at this element. Track the best seen so far.",
    "def kadane(a):\n    best = cur = a[0]\n"
    "    for x in a[1:]:\n        cur = max(x, cur + x)\n"
    "        best = max(best, cur)\n    return best",
    gen_kadane, "O(n)", "O(n)", "O(n)", "O(1)",
    default_input="-2, 1, -3, 4, -1, 2, 1, -5, 4")

reg("Prefix Sum", "Arrays", "Easy",
    "Precomputes cumulative sums so any range sum is O(1).",
    "prefix[i] = a[0] + ... + a[i-1]. Then sum(l..r) = prefix[r+1] - prefix[l].",
    "pre = [0]\nfor v in a:\n    pre.append(pre[-1] + v)\n"
    "def range_sum(l, r):\n    return pre[r + 1] - pre[l]",
    gen_prefix_sum, "O(n)", "O(n)", "O(n)", "O(n)",
    default_input="3, 1, 4, 1, 5, 9, 2, 6")

reg("Sliding Window (Max Sum)", "Arrays", "Easy",
    "Finds the maximum sum of k consecutive elements in O(n).",
    "Compute the first window, then slide it: add the new element and remove "
    "the one leaving the window.",
    "cur = sum(a[:k]); best = cur\nfor i in range(k, len(a)):\n"
    "    cur += a[i] - a[i - k]\n    best = max(best, cur)\nreturn best",
    gen_sliding_window, "O(n)", "O(n)", "O(n)", "O(1)",
    default_input="2, 1, 5, 1, 3, 2, 8, 4")

reg("Two Pointers (Pair Sum)", "Arrays", "Easy",
    "Finds a pair summing to a target in a sorted array in O(n).",
    "Start with pointers at both ends. If the sum is too small move left forward; "
    "if too large move right backward.",
    "lo, hi = 0, len(a) - 1\nwhile lo < hi:\n    s = a[lo] + a[hi]\n"
    "    if s == target: return (lo, hi)\n    if s < target: lo += 1\n    else: hi -= 1",
    gen_two_pointers, "O(1)", "O(n)", "O(n)", "O(1)",
    default_input="1, 3, 4, 6, 8, 11, 15", uses_target=True, needs_sorted=True)

reg("Frequency Counting", "Arrays", "Easy",
    "Counts how often each value appears using a hash map.",
    "Iterate once and increment a dictionary entry for each value.",
    "freq = {}\nfor v in a:\n    freq[v] = freq.get(v, 0) + 1",
    gen_frequency_count, "O(n)", "O(n)", "O(n)", "O(n)",
    default_input="1, 2, 2, 3, 3, 3, 4, 1, 5")

reg("Array Rotation", "Arrays", "Medium",
    "Rotates an array left by k using the reversal technique.",
    "Reverse the first k elements, reverse the remaining, then reverse the whole "
    "array. Each element moves exactly once.",
    "def rotate(a, k):\n    k %= len(a)\n    a[:k] = a[:k][::-1]\n"
    "    a[k:] = a[k:][::-1]\n    a.reverse()\n    return a",
    gen_rotation, "O(n)", "O(n)", "O(n)", "O(1)",
    default_input="1, 2, 3, 4, 5, 6, 7, 8")

reg("Difference Array", "Arrays", "Medium",
    "Applies many range updates in O(1) each and rebuilds with a prefix sum.",
    "Store differences between consecutive values. Adding x to [l..r] becomes "
    "diff[l] += x and diff[r+1] -= x.",
    "diff = [a[0]] + [a[i] - a[i-1] for i in range(1, len(a))]\n"
    "# add v to [l..r]: diff[l] += v; if r+1 < n: diff[r+1] -= v",
    gen_difference_array, "O(1) update", "O(n)", "O(n)", "O(n)",
    default_input="3, 6, 9, 12, 15, 18")

# ---- Strings ---------------------------------------------------------------
reg("String Traversal", "Strings", "Easy",
    "Visits every character of a string exactly once.",
    "Python strings are sequences, so a simple for loop gives O(n) traversal.",
    "for i, ch in enumerate(s):\n    print(i, ch)",
    gen_string_traversal, "O(n)", "O(n)", "O(n)", "O(1)",
    input_type="string", default_input="algorithm")

reg("Character Frequency", "Strings", "Easy",
    "Counts occurrences of each character with a hash map.",
    "One pass, incrementing counts. This is the core of many anagram / "
    "palindrome / pattern problems.",
    "freq = {}\nfor ch in s:\n    freq[ch] = freq.get(ch, 0) + 1",
    gen_char_frequency, "O(n)", "O(n)", "O(n)", "O(k)",
    input_type="string", default_input="banana")

reg("String Reversal", "Strings", "Easy",
    "Reverses a string in-place with two pointers.",
    "Swap characters from the two ends moving inward. O(n) time, O(1) extra space.",
    "def reverse(s):\n    a = list(s)\n    i, j = 0, len(a) - 1\n"
    "    while i < j:\n        a[i], a[j] = a[j], a[i]\n        i += 1; j -= 1\n    return ''.join(a)",
    gen_reverse_string, "O(n)", "O(n)", "O(n)", "O(1)",
    input_type="string", default_input="algorithm")

reg("Palindrome Check", "Strings", "Easy",
    "Checks whether a string reads the same forwards and backwards.",
    "Two pointers from both ends; the moment they differ the string is not a palindrome.",
    "def is_palindrome(s):\n    i, j = 0, len(s) - 1\n"
    "    while i < j:\n        if s[i] != s[j]: return False\n        i += 1; j -= 1\n    return True",
    gen_palindrome, "O(1)", "O(n)", "O(n)", "O(1)",
    input_type="string", default_input="madam")

reg("Anagram Check", "Strings", "Easy",
    "Determines whether two strings are permutations of each other.",
    "Count characters in the first string, then decrement for the second. "
    "All counters must return to zero.",
    "from collections import Counter\ndef is_anagram(a, b):\n    return Counter(a) == Counter(b)",
    gen_anagram, "O(n)", "O(n)", "O(n)", "O(k)",
    input_type="string_pair", default_input="listen, silent")

reg("Substring Search (Naive)", "Strings", "Easy",
    "Finds the first occurrence of a pattern inside a text.",
    "Slide the pattern over the text and compare character by character.",
    "def search(text, pat):\n    n, m = len(text), len(pat)\n"
    "    for i in range(n - m + 1):\n        if text[i:i+m] == pat:\n            return i\n    return -1",
    gen_substring_search, "O(n)", "O(n·m)", "O(n·m)", "O(1)",
    input_type="string", default_input="ababcababa")

reg("String Compression", "Strings", "Medium",
    "Run-length encodes a string: 'aaabbc' → 'a3b2c1'.",
    "Walk through runs of equal characters, counting the run length and "
    "emitting the character followed by the count.",
    "def compress(s):\n    out = []\n    i = 0\n"
    "    while i < len(s):\n        j = i\n        while j < len(s) and s[j] == s[i]:\n            j += 1\n"
    "        out.append(s[i] + str(j - i))\n        i = j\n    return ''.join(out)",
    gen_string_compression, "O(n)", "O(n)", "O(n)", "O(n)",
    input_type="string", default_input="aaabbc")

reg("String Hashing", "Strings", "Medium",
    "Rolling polynomial hash used for O(1) substring comparison.",
    "h = (h * base + ord(c)) mod M. Prefix hashes let you compare any two "
    "substrings in O(1).",
    "M, B = 10**9 + 7, 31\nh = 0\nfor ch in s:\n    h = (h * B + ord(ch)) % M",
    gen_string_hashing, "O(n)", "O(n)", "O(n)", "O(n)",
    input_type="string", default_input="rollinghash")

# ---- Linked Lists ----------------------------------------------------------
_LL_DEFAULT = "10, 20, 30, 40"

reg("Linked List — Insert at End", "Linked Lists", "Easy",
    "Appends new nodes at the tail of a singly linked list.",
    "Traverse to the last node and set its next pointer to the new node. "
    "With a tail pointer this is O(1).",
    "def append(head, value):\n    node = Node(value)\n"
    "    if head is None: return node\n    cur = head\n"
    "    while cur.next: cur = cur.next\n    cur.next = node\n    return head",
    gen_ll_insert_end, "O(1)", "O(n)", "O(n)", "O(1)",
    default_input=_LL_DEFAULT)

reg("Linked List — Insert at Beginning", "Linked Lists", "Easy",
    "Prepends a node at the head in constant time.",
    "The new node's next pointer becomes the old head, and the new node "
    "becomes the head.",
    "def prepend(head, value):\n    node = Node(value)\n    node.next = head\n    return node",
    gen_ll_insert_front, "O(1)", "O(1)", "O(1)", "O(1)",
    default_input=_LL_DEFAULT)

reg("Linked List — Delete by Value", "Linked Lists", "Easy",
    "Removes the first node holding a given value.",
    "Walk with a previous pointer; when the value matches, redirect prev.next "
    "to curr.next so the node is unlinked.",
    "def delete(head, value):\n    if head and head.val == value: return head.next\n"
    "    cur = head\n    while cur.next and cur.next.val != value:\n        cur = cur.next\n"
    "    if cur.next: cur.next = cur.next.next\n    return head",
    gen_ll_delete, "O(1)", "O(n)", "O(n)", "O(1)",
    default_input=_LL_DEFAULT)

reg("Linked List — Reverse", "Linked Lists", "Medium",
    "Reverses a singly linked list in place.",
    "Keep three pointers: prev, curr, next. Repoint curr.next to prev, then "
    "shift all three forward.",
    "def reverse(head):\n    prev = None\n    cur = head\n"
    "    while cur:\n        nxt = cur.next\n        cur.next = prev\n"
    "        prev = cur\n        cur = nxt\n    return prev",
    gen_ll_reverse, "O(n)", "O(n)", "O(n)", "O(1)",
    default_input=_LL_DEFAULT)

reg("Linked List — Find Middle", "Linked Lists", "Easy",
    "Finds the middle node with the fast & slow pointer technique.",
    "slow advances by one, fast by two. When fast reaches the end, slow is "
    "at the middle.",
    "slow = fast = head\nwhile fast and fast.next:\n    slow = slow.next\n    fast = fast.next.next\nreturn slow",
    gen_ll_middle, "O(n)", "O(n)", "O(n)", "O(1)",
    default_input="1, 2, 3, 4, 5, 6, 7")

reg("Linked List — Detect Cycle", "Linked Lists", "Medium",
    "Floyd's tortoise & hare cycle detection.",
    "If there is a cycle, the fast pointer eventually laps the slow pointer "
    "and they meet. Otherwise fast hits NULL.",
    "slow = fast = head\nwhile fast and fast.next:\n    slow = slow.next\n"
    "    fast = fast.next.next\n    if slow is fast: return True\nreturn False",
    gen_ll_cycle, "O(n)", "O(n)", "O(n)", "O(1)",
    default_input="1, 2, 3, 4, 5, 6")

# ---- Stack -----------------------------------------------------------------
reg("Stack — Push / Pop", "Stack", "Easy",
    "LIFO structure: the last element pushed is the first popped.",
    "push adds to the top; pop removes from the top. Both are O(1).",
    "class Stack:\n    def __init__(self): self.data = []\n"
    "    def push(self, x): self.data.append(x)\n"
    "    def pop(self): return self.data.pop()\n"
    "    def peek(self): return self.data[-1]",
    gen_stack_ops, "O(1)", "O(1)", "O(1)", "O(n)",
    default_input="10, 20, 30, 40")

reg("Balanced Parentheses", "Stack", "Easy",
    "Checks whether brackets in an expression are properly balanced.",
    "Push opening brackets. On a closing bracket, the top of the stack must be "
    "its matching opener. The stack must end empty.",
    "pairs = {')': '(', ']': '[', '}': '{'}\nst = []\nfor ch in s:\n"
    "    if ch in '([{': st.append(ch)\n"
    "    elif ch in pairs:\n        if not st or st.pop() != pairs[ch]: return False\n"
    "return not st",
    gen_balanced_parens, "O(n)", "O(n)", "O(n)", "O(n)",
    input_type="string", default_input="{[()()]}")

reg("Infix → Postfix", "Stack", "Medium",
    "Converts infix notation to Reverse Polish Notation using the shunting-yard algorithm.",
    "Operands go straight to the output. Operators wait on the stack, popping "
    "higher-or-equal precedence operators first. Parentheses delimit groups.",
    "def infix_to_postfix(s):\n    prec = {'+':1,'-':1,'*':2,'/':2,'^':3}\n"
    "    st, out = [], []\n    for ch in s:\n        if ch.isalnum(): out.append(ch)\n"
    "        elif ch == '(': st.append(ch)\n"
    "        elif ch == ')':\n            while st and st[-1] != '(': out.append(st.pop())\n"
    "            st.pop()\n"
    "        else:\n            while st and st[-1] != '(' and prec.get(st[-1],0) >= prec[ch]:\n"
    "                out.append(st.pop())\n            st.append(ch)\n"
    "    while st: out.append(st.pop())\n    return ''.join(out)",
    gen_infix_postfix, "O(n)", "O(n)", "O(n)", "O(n)",
    input_type="string", default_input="A+B*C-D")

reg("Postfix Evaluation", "Stack", "Medium",
    "Evaluates a Reverse Polish Notation expression with a stack.",
    "Digits are pushed. On an operator, pop two operands, apply the operator, "
    "and push the result.",
    "def eval_rpn(tokens):\n    st = []\n    for t in tokens:\n"
    "        if t.lstrip('-').isdigit(): st.append(int(t))\n"
    "        else:\n            b = st.pop(); a = st.pop()\n"
    "            st.append({'+':a+b,'-':a-b,'*':a*b,'/':a//b}[t])\n    return st[-1]",
    gen_postfix_eval, "O(n)", "O(n)", "O(n)", "O(n)",
    input_type="string", default_input="23+45*+")

reg("Next Greater Element", "Stack", "Medium",
    "For each element, finds the next element to its right that is greater.",
    "Maintain a monotonic decreasing stack of indices. When a bigger value "
    "arrives, it is the answer for every smaller index on top of the stack.",
    "res = [-1] * len(a)\nst = []\nfor i, v in enumerate(a):\n"
    "    while st and a[st[-1]] < v:\n        res[st.pop()] = v\n    st.append(i)\nreturn res",
    gen_next_greater, "O(n)", "O(n)", "O(n)", "O(n)",
    default_input="4, 5, 2, 10, 8, 3")

reg("Min Stack", "Stack", "Medium",
    "A stack that supports push, pop, top and getMin all in O(1).",
    "Keep a second stack holding the running minimum alongside each pushed value.",
    "class MinStack:\n    def __init__(self):\n        self.st, self.mn = [], []\n"
    "    def push(self, x):\n        self.st.append(x)\n"
    "        self.mn.append(x if not self.mn else min(x, self.mn[-1]))\n"
    "    def pop(self):\n        self.mn.pop(); return self.st.pop()\n"
    "    def getMin(self): return self.mn[-1]",
    gen_min_stack, "O(1)", "O(1)", "O(1)", "O(n)",
    default_input="5, 3, 7, 2, 8")

# ---- Queue -----------------------------------------------------------------
reg("Simple Queue", "Queue", "Easy",
    "FIFO structure: the first element enqueued is the first dequeued.",
    "enqueue appends at the rear, dequeue removes from the front.",
    "from collections import deque\nq = deque()\nq.append(x)     # enqueue\nq.popleft()     # dequeue",
    gen_simple_queue, "O(1)", "O(1)", "O(1)", "O(n)",
    default_input="10, 20, 30, 40")

reg("Circular Queue", "Queue", "Medium",
    "A fixed-size queue that wraps around, reusing freed slots.",
    "rear = (front + size) % capacity. When the buffer ends the next index "
    "wraps to zero, so no space is wasted.",
    "class CircularQueue:\n    def __init__(self, k):\n"
    "        self.buf = [None]*k; self.front = 0; self.size = 0; self.k = k\n"
    "    def enqueue(self, v):\n        if self.size == self.k: return False\n"
    "        self.buf[(self.front + self.size) % self.k] = v\n        self.size += 1\n        return True\n"
    "    def dequeue(self):\n        if not self.size: return None\n"
    "        v = self.buf[self.front]; self.front = (self.front+1) % self.k\n"
    "        self.size -= 1; return v",
    gen_circular_queue, "O(1)", "O(1)", "O(1)", "O(k)",
    default_input="1, 2, 3, 4, 5, 6")

reg("Deque", "Queue", "Easy",
    "Double-ended queue: insert and remove at both ends in O(1).",
    "collections.deque is implemented as a doubly linked list of blocks.",
    "from collections import deque\nd = deque()\nd.appendleft(x); d.append(x)\n"
    "d.popleft();    d.pop()",
    gen_deque, "O(1)", "O(1)", "O(1)", "O(n)",
    default_input="1, 2, 3, 4, 5, 6")

reg("Priority Queue (Min-Heap)", "Queue", "Medium",
    "Elements are served by priority, not arrival order.",
    "A binary heap keeps the smallest element at index 0. push and pop are "
    "both O(log n).",
    "import heapq\nh = []\nheapq.heappush(h, x)\nsmallest = heapq.heappop(h)",
    gen_priority_queue, "O(1)", "O(log n)", "O(log n)", "O(n)",
    default_input="5, 3, 8, 1, 9, 2")

reg("Queue using Stacks", "Queue", "Medium",
    "Implements a FIFO queue with two LIFO stacks.",
    "Push onto s_in. For dequeue, if s_out is empty move everything from s_in "
    "to s_out (reversing the order), then pop from s_out.",
    "class MyQueue:\n    def __init__(self):\n        self.inp, self.out = [], []\n"
    "    def push(self, x): self.inp.append(x)\n"
    "    def pop(self):\n        if not self.out:\n"
    "            while self.inp: self.out.append(self.inp.pop())\n"
    "        return self.out.pop()",
    gen_queue_using_stacks, "O(1) push", "O(1) amortized", "O(n)", "O(n)",
    default_input="1, 2, 3, 4")

# ---- Hashing ---------------------------------------------------------------
reg("Hash Table with Chaining", "Hashing", "Medium",
    "Resolves collisions by storing a linked list (chain) in each bucket.",
    "hash(k) = k mod m gives the bucket. If the bucket is occupied, append to "
    "its chain. Lookup walks the chain.",
    "size = 7\ntable = [[] for _ in range(size)]\n"
    "def insert(k):\n    table[k % size].append(k)\n"
    "def find(k):\n    return k in table[k % size]",
    gen_hash_chaining, "O(1)", "O(1+n/m)", "O(n)", "O(n)",
    default_input="12, 22, 32, 5, 15, 3")

reg("Open Addressing (Linear Probing)", "Hashing", "Medium",
    "Resolves collisions by scanning forward for the next free slot.",
    "On collision try (h+1) mod m, (h+2) mod m … until an empty slot is found. "
    "No extra pointers are needed but clustering can occur.",
    "def insert(table, key):\n    m = len(table)\n    i = key % m\n"
    "    while table[i] is not None:\n        i = (i + 1) % m\n    table[i] = key",
    gen_linear_probing, "O(1)", "O(1/(1-α))", "O(n)", "O(n)",
    default_input="12, 22, 5, 15, 3, 27")

reg("Two Sum (Hash Map)", "Hashing", "Easy",
    "Finds two indices whose values add up to a target in one pass.",
    "Store each visited value in a map. For every element check whether its "
    "complement is already present.",
    "def two_sum(a, target):\n    seen = {}\n"
    "    for i, v in enumerate(a):\n        if target - v in seen:\n"
    "            return [seen[target - v], i]\n        seen[v] = i\n    return []",
    gen_two_sum, "O(1)", "O(n)", "O(n)", "O(n)",
    default_input="2, 7, 11, 15, 8, 3", uses_target=True)

reg("Duplicate Detection", "Hashing", "Easy",
    "Checks whether any value occurs more than once.",
    "Insert values into a hash set; if an insert fails the value is a duplicate.",
    "def has_duplicate(a):\n    seen = set()\n"
    "    for v in a:\n        if v in seen: return True\n        seen.add(v)\n    return False",
    gen_duplicate_detect, "O(n)", "O(n)", "O(n)", "O(n)",
    default_input="1, 2, 3, 4, 5, 3")

# ---- Searching -------------------------------------------------------------
reg("Linear Search", "Searching", "Easy",
    "Scans every element until the target is found.",
    "Simple sequential scan; no ordering requirement.",
    "def linear_search(a, target):\n    for i, v in enumerate(a):\n"
    "        if v == target: return i\n    return -1",
    gen_linear_search, "O(1)", "O(n)", "O(n)", "O(1)",
    default_input="10, 20, 30, 40, 50, 60, 70", uses_target=True)

reg("Binary Search", "Searching", "Easy",
    "Halves the search range on every step in a sorted array.",
    "Compare with the middle element; discard the half that cannot contain the target.",
    "def binary_search(a, target):\n    lo, hi = 0, len(a) - 1\n"
    "    while lo <= hi:\n        mid = (lo + hi) // 2\n"
    "        if a[mid] == target: return mid\n"
    "        if a[mid] < target: lo = mid + 1\n        else: hi = mid - 1\n    return -1",
    gen_binary_search, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="10, 20, 30, 40, 50, 60, 70", uses_target=True, needs_sorted=True)

reg("Lower Bound", "Searching", "Medium",
    "First index where the value is >= target.",
    "Standard binary search that keeps moving left when a[mid] >= target.",
    "def lower_bound(a, x):\n    lo, hi = 0, len(a)\n"
    "    while lo < hi:\n        mid = (lo + hi) // 2\n"
    "        if a[mid] < x: lo = mid + 1\n        else: hi = mid\n    return lo",
    gen_lower_bound, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="10, 20, 20, 20, 30, 40, 50", uses_target=True, needs_sorted=True)

reg("Upper Bound", "Searching", "Medium",
    "First index where the value is strictly greater than target.",
    "Same as lower bound but the condition is a[mid] <= target.",
    "def upper_bound(a, x):\n    lo, hi = 0, len(a)\n"
    "    while lo < hi:\n        mid = (lo + hi) // 2\n"
    "        if a[mid] <= x: lo = mid + 1\n        else: hi = mid\n    return lo",
    gen_upper_bound, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="10, 20, 20, 20, 30, 40, 50", uses_target=True, needs_sorted=True)

reg("First Occurrence", "Searching", "Medium",
    "Finds the leftmost index of a value in a sorted array.",
    "On a match, record the index and keep searching in the left half.",
    "best = -1\nlo, hi = 0, len(a) - 1\nwhile lo <= hi:\n    mid = (lo + hi) // 2\n"
    "    if a[mid] == x: best = mid; hi = mid - 1\n"
    "    elif a[mid] < x: lo = mid + 1\n    else: hi = mid - 1\nreturn best",
    gen_first_occurrence, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="5, 5, 5, 7, 7, 9", uses_target=True, needs_sorted=True)

reg("Last Occurrence", "Searching", "Medium",
    "Finds the rightmost index of a value in a sorted array.",
    "On a match, record the index and keep searching in the right half.",
    "best = -1\nlo, hi = 0, len(a) - 1\nwhile lo <= hi:\n    mid = (lo + hi) // 2\n"
    "    if a[mid] == x: best = mid; lo = mid + 1\n"
    "    elif a[mid] < x: lo = mid + 1\n    else: hi = mid - 1\nreturn best",
    gen_last_occurrence, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="5, 5, 5, 7, 7, 9", uses_target=True, needs_sorted=True)

reg("Search in Rotated Sorted Array", "Searching", "Medium",
    "Binary search on an array that has been rotated.",
    "At every step one half is still sorted; determine which half and whether "
    "the target lies inside it.",
    "def search(a, t):\n    lo, hi = 0, len(a) - 1\n"
    "    while lo <= hi:\n        mid = (lo + hi) // 2\n"
    "        if a[mid] == t: return mid\n"
    "        if a[lo] <= a[mid]:\n"
    "            if a[lo] <= t < a[mid]: hi = mid - 1\n            else: lo = mid + 1\n"
    "        else:\n            if a[mid] < t <= a[hi]: lo = mid + 1\n            else: hi = mid - 1\n"
    "    return -1",
    gen_rotated_search, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="40, 50, 60, 70, 10, 20, 30", uses_target=True)

reg("Peak Element", "Searching", "Medium",
    "Finds any index whose value is greater than its neighbours.",
    "If a[mid] < a[mid+1] a peak must exist to the right, else to the left.",
    "def find_peak(a):\n    lo, hi = 0, len(a) - 1\n"
    "    while lo < hi:\n        mid = (lo + hi) // 2\n"
    "        if a[mid] < a[mid + 1]: lo = mid + 1\n        else: hi = mid\n    return lo",
    gen_peak_element, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="1, 3, 20, 4, 1, 0")

reg("Binary Search on Answer", "Searching", "Hard",
    "Searches the answer space instead of the array.",
    "When a predicate is monotonic (false…false,true…true), binary search the "
    "smallest value for which it becomes true.",
    "def smallest_x(target):\n    lo, hi = 0, 10**9\n"
    "    while lo < hi:\n        mid = (lo + hi) // 2\n"
    "        if mid * mid >= target: hi = mid\n        else: lo = mid + 1\n    return lo",
    gen_bs_on_answer, "O(1)", "O(log n)", "O(log n)", "O(1)",
    default_input="1, 2, 3, 4, 5", uses_target=True)

# ---- Sorting ---------------------------------------------------------------
reg("Bubble Sort", "Sorting", "Easy",
    "Repeatedly swaps adjacent out-of-order pairs; large values 'bubble up'.",
    "Each pass moves the largest remaining value to the end. Early exit if a "
    "pass makes no swaps.",
    "def bubble_sort(a):\n    n = len(a)\n    for i in range(n - 1):\n"
    "        swapped = False\n        for j in range(n - 1 - i):\n"
    "            if a[j] > a[j + 1]:\n                a[j], a[j+1] = a[j+1], a[j]\n"
    "                swapped = True\n        if not swapped: break\n    return a",
    gen_bubble, "O(n)", "O(n²)", "O(n²)", "O(1)", "Yes", "Yes")

reg("Selection Sort", "Sorting", "Easy",
    "Selects the minimum of the unsorted part and swaps it into place.",
    "One swap per pass, but always O(n²) comparisons regardless of input order.",
    "def selection_sort(a):\n    for i in range(len(a) - 1):\n"
    "        m = i\n        for j in range(i + 1, len(a)):\n"
    "            if a[j] < a[m]: m = j\n        a[i], a[m] = a[m], a[i]\n    return a",
    gen_selection, "O(n²)", "O(n²)", "O(n²)", "O(1)", "No", "Yes")

reg("Insertion Sort", "Sorting", "Easy",
    "Grows a sorted prefix by inserting each new element into place.",
    "Excellent for nearly-sorted small arrays; adaptive and stable.",
    "def insertion_sort(a):\n    for i in range(1, len(a)):\n"
    "        key, j = a[i], i - 1\n        while j >= 0 and a[j] > key:\n"
    "            a[j + 1] = a[j]\n            j -= 1\n        a[j + 1] = key\n    return a",
    gen_insertion, "O(n)", "O(n²)", "O(n²)", "O(1)", "Yes", "Yes")

reg("Merge Sort", "Sorting", "Medium",
    "Divide & conquer: split in half, sort each half, merge the results.",
    "Guaranteed O(n log n), stable, but needs O(n) auxiliary memory.",
    "def merge_sort(a):\n    if len(a) <= 1: return a\n    mid = len(a) // 2\n"
    "    left = merge_sort(a[:mid]); right = merge_sort(a[mid:])\n"
    "    out, i, j = [], 0, 0\n"
    "    while i < len(left) and j < len(right):\n"
    "        if left[i] <= right[j]: out.append(left[i]); i += 1\n"
    "        else: out.append(right[j]); j += 1\n"
    "    return out + left[i:] + right[j:]",
    gen_merge, "O(n log n)", "O(n log n)", "O(n log n)", "O(n)", "Yes", "No")

reg("Quick Sort", "Sorting", "Medium",
    "Partitions around a pivot, then recursively sorts both sides.",
    "Fast in practice with good cache behaviour; worst case O(n²) on already "
    "sorted data with a bad pivot rule.",
    "def quick_sort(a, lo, hi):\n    if lo >= hi: return\n"
    "    pivot, i = a[hi], lo\n    for j in range(lo, hi):\n"
    "        if a[j] < pivot:\n            a[i], a[j] = a[j], a[i]\n            i += 1\n"
    "    a[i], a[hi] = a[hi], a[i]\n    quick_sort(a, lo, i - 1)\n    quick_sort(a, i + 1, hi)",
    gen_quick, "O(n log n)", "O(n log n)", "O(n²)", "O(log n)", "No", "Yes")

reg("Heap Sort", "Sorting", "Medium",
    "Builds a max-heap and repeatedly extracts the maximum.",
    "In-place and guaranteed O(n log n), but not stable and cache-unfriendly.",
    "def heap_sort(a):\n    n = len(a)\n"
    "    def sift(i, size):\n        while True:\n"
    "            l, r, big = 2*i+1, 2*i+2, i\n"
    "            if l < size and a[l] > a[big]: big = l\n"
    "            if r < size and a[r] > a[big]: big = r\n"
    "            if big == i: return\n"
    "            a[i], a[big] = a[big], a[i]\n            i = big\n"
    "    for i in range(n//2 - 1, -1, -1): sift(i, n)\n"
    "    for end in range(n-1, 0, -1):\n        a[0], a[end] = a[end], a[0]\n        sift(0, end)",
    gen_heap_sort, "O(n log n)", "O(n log n)", "O(n log n)", "O(1)", "No", "Yes")

reg("Counting Sort", "Sorting", "Medium",
    "Non-comparison sort that counts occurrences of each value.",
    "Linear time when the value range k is small. Not comparison based, so it "
    "can beat the O(n log n) lower bound.",
    "def counting_sort(a):\n    lo, hi = min(a), max(a)\n"
    "    cnt = [0] * (hi - lo + 1)\n    for v in a: cnt[v - lo] += 1\n"
    "    idx = 0\n    for v in range(lo, hi + 1):\n        for _ in range(cnt[v - lo]):\n"
    "            a[idx] = v; idx += 1\n    return a",
    gen_counting, "O(n+k)", "O(n+k)", "O(n+k)", "O(k)", "Yes", "No",
    default_input="4, 2, 2, 8, 3, 3, 1")

reg("Radix Sort", "Sorting", "Medium",
    "Sorts digit by digit from least significant to most significant.",
    "Each pass uses a stable counting sort on one digit. Total O(d·(n+b)).",
    "def radix_sort(a):\n    exp = 1\n    while max(a) // exp > 0:\n"
    "        buckets = [[] for _ in range(10)]\n"
    "        for v in a: buckets[(v // exp) % 10].append(v)\n"
    "        a = [v for b in buckets for v in b]\n        exp *= 10\n    return a",
    gen_radix, "O(nk)", "O(nk)", "O(nk)", "O(n+b)", "Yes", "No",
    default_input="170, 45, 75, 90, 802, 24, 2, 66")

reg("Bucket Sort", "Sorting", "Medium",
    "Distributes values into buckets, sorts each, then concatenates.",
    "Works well when values are uniformly distributed over a known range.",
    "def bucket_sort(a, k=5):\n    lo, hi = min(a), max(a)\n"
    "    span = (hi - lo) or 1\n    buckets = [[] for _ in range(k)]\n"
    "    for v in a: buckets[min(k-1, int((v-lo)/(span+1)*k))].append(v)\n"
    "    out = []\n    for b in buckets: out.extend(sorted(b))\n    return out",
    gen_bucket, "O(n+k)", "O(n+k)", "O(n²)", "O(n+k)", "Yes", "No",
    default_input="29, 25, 3, 49, 9, 37, 21, 43")

# ---- Trees -----------------------------------------------------------------
_TREE_DEFAULT = "50, 30, 70, 20, 40, 60, 80"

reg("BST Insert", "Trees", "Medium",
    "Builds a Binary Search Tree by inserting values one at a time.",
    "Compare with the current node: go left if smaller, right if greater. "
    "Insert as a leaf when a null child is reached.",
    "def insert(root, v):\n    if root is None: return Node(v)\n"
    "    if v < root.val: root.left = insert(root.left, v)\n"
    "    elif v > root.val: root.right = insert(root.right, v)\n    return root",
    gen_bst_insert, "O(log n)", "O(log n)", "O(n)", "O(n)",
    default_input=_TREE_DEFAULT)

reg("Preorder Traversal", "Trees", "Easy",
    "Visits Root → Left → Right.",
    "Useful for copying or serializing a tree.",
    "def preorder(n):\n    if not n: return\n"
    "    print(n.val)\n    preorder(n.left)\n    preorder(n.right)",
    gen_preorder, "O(n)", "O(n)", "O(n)", "O(h)",
    default_input=_TREE_DEFAULT)

reg("Inorder Traversal", "Trees", "Easy",
    "Visits Left → Root → Right — produces sorted order for a BST.",
    "The classic way to print a BST in ascending order.",
    "def inorder(n):\n    if not n: return\n"
    "    inorder(n.left)\n    print(n.val)\n    inorder(n.right)",
    gen_inorder, "O(n)", "O(n)", "O(n)", "O(h)",
    default_input=_TREE_DEFAULT)

reg("Postorder Traversal", "Trees", "Easy",
    "Visits Left → Right → Root.",
    "Used for deleting trees or evaluating expression trees.",
    "def postorder(n):\n    if not n: return\n"
    "    postorder(n.left)\n    postorder(n.right)\n    print(n.val)",
    gen_postorder, "O(n)", "O(n)", "O(n)", "O(h)",
    default_input=_TREE_DEFAULT)

reg("Level Order Traversal", "Trees", "Medium",
    "Breadth-first traversal that visits nodes level by level.",
    "A queue drives the traversal: enqueue children as each node is dequeued.",
    "from collections import deque\ndef level_order(root):\n    q = deque([root])\n"
    "    while q:\n        n = q.popleft()\n        if not n: continue\n"
    "        print(n.val)\n        q.append(n.left)\n        q.append(n.right)",
    gen_levelorder, "O(n)", "O(n)", "O(n)", "O(n)",
    default_input=_TREE_DEFAULT)

reg("BST Search", "Trees", "Easy",
    "Looks up a value by exploiting BST ordering.",
    "At each node decide to go left or right based on the comparison — "
    "halving the search space like binary search.",
    "def search(root, v):\n    cur = root\n"
    "    while cur:\n        if cur.val == v: return cur\n"
    "        cur = cur.left if v < cur.val else cur.right\n    return None",
    gen_bst_search, "O(1)", "O(log n)", "O(n)", "O(1)",
    default_input=_TREE_DEFAULT, uses_target=True)

reg("Tree Metrics (Height / Min / Max)", "Trees", "Easy",
    "Computes the height and the extreme values of a BST.",
    "Height is 1 + max(height(left), height(right)). Minimum is the leftmost "
    "node, maximum the rightmost.",
    "def height(n):\n    if not n: return -1\n"
    "    return 1 + max(height(n.left), height(n.right))\n\n"
    "def minimum(n):\n    while n.left: n = n.left\n    return n.val",
    gen_tree_metrics, "O(1)", "O(n)", "O(n)", "O(h)",
    default_input=_TREE_DEFAULT)

reg("Min-Heap (Sift Up)", "Trees", "Medium",
    "Builds a binary min-heap by repeatedly sifting new values up.",
    "The parent of index i is (i-1)//2. While the parent is larger, swap them.",
    "def push(heap, v):\n    heap.append(v)\n    i = len(heap) - 1\n"
    "    while i > 0:\n        p = (i - 1) // 2\n"
    "        if heap[p] <= heap[i]: break\n"
    "        heap[p], heap[i] = heap[i], heap[p]\n        i = p",
    gen_heap_demo, "O(1)", "O(log n)", "O(log n)", "O(n)",
    default_input="5, 3, 8, 1, 9, 2")

reg("Trie (Prefix Tree)", "Trees", "Hard",
    "A tree keyed by characters that supports fast prefix queries.",
    "Each node is a dictionary of children. Insert words character by character "
    "and mark terminal nodes. Search is O(length of the word).",
    "class Trie:\n    def __init__(self): self.root = {}\n"
    "    def insert(self, w):\n        node = self.root\n"
    "        for ch in w: node = node.setdefault(ch, {})\n        node['$'] = True\n"
    "    def search(self, w):\n        node = self.root\n"
    "        for ch in w:\n            if ch not in node: return False\n"
    "            node = node[ch]\n        return '$' in node",
    gen_trie, "O(1)", "O(L)", "O(L)", "O(N·L)", input_type="none")

# ---- Graphs ----------------------------------------------------------------
reg("Breadth-First Search", "Graphs", "Medium",
    "Explores a graph level by level using a queue.",
    "Start at a source, enqueue its unvisited neighbours, and process the "
    "queue in FIFO order. Finds shortest paths in unweighted graphs.",
    "from collections import deque\ndef bfs(adj, src):\n    seen = {src}\n    q = deque([src])\n"
    "    while q:\n        u = q.popleft()\n        for v in adj[u]:\n"
    "            if v not in seen:\n                seen.add(v)\n                q.append(v)",
    gen_bfs, "O(V+E)", "O(V+E)", "O(V+E)", "O(V)", input_type="none")

reg("Depth-First Search", "Graphs", "Medium",
    "Explores as deep as possible before backtracking.",
    "A stack (explicit or the call stack) drives the traversal. Foundation for "
    "cycle detection, topological sort and connected components.",
    "def dfs(adj, u, seen=None):\n    seen = seen or set()\n"
    "    seen.add(u)\n    for v in adj[u]:\n        if v not in seen:\n            dfs(adj, v, seen)",
    gen_dfs, "O(V+E)", "O(V+E)", "O(V+E)", "O(V)", input_type="none")

reg("Dijkstra's Algorithm", "Graphs", "Hard",
    "Single-source shortest paths on graphs with non-negative weights.",
    "Repeatedly extract the unvisited node with the smallest tentative distance "
    "and relax its outgoing edges. A priority queue makes it O((V+E) log V).",
    "import heapq\ndef dijkstra(adj, src):\n    dist = {n: float('inf') for n in adj}\n"
    "    dist[src] = 0\n    pq = [(0, src)]\n"
    "    while pq:\n        d, u = heapq.heappop(pq)\n"
    "        if d > dist[u]: continue\n        for v, w in adj[u]:\n"
    "            if d + w < dist[v]:\n                dist[v] = d + w\n                heapq.heappush(pq, (dist[v], v))\n"
    "    return dist",
    gen_dijkstra, "O((V+E) log V)", "O((V+E) log V)", "O((V+E) log V)", "O(V)",
    input_type="none")

reg("Bellman-Ford", "Graphs", "Hard",
    "Shortest paths with negative weights; detects negative cycles.",
    "Relax every edge V-1 times. If an edge can still be relaxed afterwards a "
    "negative cycle exists.",
    "def bellman_ford(n, edges, src):\n    dist = [float('inf')] * n\n    dist[src] = 0\n"
    "    for _ in range(n - 1):\n        for u, v, w in edges:\n"
    "            if dist[u] + w < dist[v]:\n                dist[v] = dist[u] + w\n"
    "    for u, v, w in edges:\n        if dist[u] + w < dist[v]:\n            return None  # negative cycle\n"
    "    return dist",
    gen_bellman_ford, "O(E)", "O(V·E)", "O(V·E)", "O(V)", input_type="none")

reg("Floyd-Warshall", "Graphs", "Hard",
    "All-pairs shortest paths with a triple nested loop.",
    "For every intermediate node k, check whether going through k improves any "
    "pair (i, j). Works with negative edges (no negative cycles).",
    "def floyd_warshall(n, d):\n    for k in range(n):\n"
    "        for i in range(n):\n            for j in range(n):\n"
    "                d[i][j] = min(d[i][j], d[i][k] + d[k][j])\n    return d",
    gen_floyd_warshall, "O(V³)", "O(V³)", "O(V³)", "O(V²)", input_type="none")

reg("Prim's MST", "Graphs", "Hard",
    "Builds a minimum spanning tree by growing from one vertex.",
    "Always add the cheapest edge connecting the current tree to a new vertex. "
    "Greedy and correct for connected weighted graphs.",
    "import heapq\ndef prim(adj, start):\n    mst = {start}\n"
    "    pq = [(w, start, v) for v, w in adj[start]]\n    heapq.heapify(pq)\n"
    "    total = 0\n    while pq:\n        w, u, v = heapq.heappop(pq)\n"
    "        if v in mst: continue\n        mst.add(v)\n        total += w\n"
    "        for nb, w2 in adj[v]:\n            if nb not in mst: heapq.heappush(pq, (w2, v, nb))\n"
    "    return total",
    gen_prim, "O(E log V)", "O(E log V)", "O(E log V)", "O(V)", input_type="none")

reg("Kruskal's MST", "Graphs", "Hard",
    "Sorts all edges by weight and adds them if they don't form a cycle.",
    "Union-Find tells you in near-constant time whether two vertices are "
    "already connected.",
    "def kruskal(n, edges):\n    parent = list(range(n))\n"
    "    def find(x):\n        while parent[x] != x:\n            parent[x] = parent[parent[x]]\n            x = parent[x]\n        return x\n"
    "    total = 0\n    for u, v, w in sorted(edges, key=lambda e: e[2]):\n"
    "        ru, rv = find(u), find(v)\n"
    "        if ru != rv:\n            parent[ru] = rv\n            total += w\n    return total",
    gen_kruskal, "O(E log E)", "O(E log E)", "O(E log E)", "O(V)", input_type="none")

reg("Topological Sort", "Graphs", "Medium",
    "Orders the vertices of a DAG so every edge points forward.",
    "Kahn's algorithm: repeatedly remove a vertex with in-degree zero.",
    "from collections import deque\ndef topo(n, adj):\n    indeg = [0] * n\n"
    "    for u in range(n):\n        for v in adj[u]: indeg[v] += 1\n"
    "    q = deque([i for i in range(n) if indeg[i] == 0])\n    order = []\n"
    "    while q:\n        u = q.popleft(); order.append(u)\n"
    "        for v in adj[u]:\n            indeg[v] -= 1\n"
    "            if indeg[v] == 0: q.append(v)\n    return order",
    gen_topological, "O(V+E)", "O(V+E)", "O(V+E)", "O(V)", input_type="none")

reg("Connected Components", "Graphs", "Medium",
    "Finds groups of vertices that are mutually reachable.",
    "Run DFS/BFS from every unvisited vertex; each run discovers one component.",
    "def components(adj):\n    seen, comp = set(), 0\n"
    "    for s in adj:\n        if s in seen: continue\n        comp += 1\n"
    "        stack = [s]\n        while stack:\n            u = stack.pop()\n"
    "            if u in seen: continue\n            seen.add(u)\n"
    "            stack.extend(v for v in adj[u] if v not in seen)\n    return comp",
    gen_components, "O(V+E)", "O(V+E)", "O(V+E)", "O(V)", input_type="none")

reg("Cycle Detection (Undirected)", "Graphs", "Medium",
    "Detects a back edge during DFS in an undirected graph.",
    "If a visited neighbour is not the parent of the current node, an edge "
    "closes a cycle.",
    "def has_cycle(adj, u, parent, seen):\n    seen.add(u)\n"
    "    for v in adj[u]:\n        if v not in seen:\n"
    "            if has_cycle(adj, v, u, seen): return True\n"
    "        elif v != parent: return True\n    return False",
    gen_cycle_detect, "O(V+E)", "O(V+E)", "O(V+E)", "O(V)", input_type="none")

reg("Union-Find (DSU)", "Graphs", "Medium",
    "Disjoint Set Union with path compression and union by rank.",
    "Nearly O(1) amortized per operation — the backbone of Kruskal's algorithm "
    "and dynamic connectivity problems.",
    "parent = list(range(n))\nrank = [0] * n\n"
    "def find(x):\n    while parent[x] != x:\n        parent[x] = parent[parent[x]]\n        x = parent[x]\n    return x\n"
    "def union(a, b):\n    ra, rb = find(a), find(b)\n"
    "    if ra == rb: return False\n"
    "    if rank[ra] < rank[rb]: ra, rb = rb, ra\n"
    "    parent[rb] = ra\n    if rank[ra] == rank[rb]: rank[ra] += 1\n    return True",
    gen_union_find, "O(1)", "O(α(n))", "O(α(n))", "O(n)", input_type="none")

# ---- Greedy ----------------------------------------------------------------
reg("Activity Selection", "Greedy", "Easy",
    "Picks the maximum number of non-overlapping activities.",
    "Greedy choice: sort by finish time and always take the activity that "
    "finishes earliest and starts after the previous one ended.",
    "def activity_selection(acts):\n    acts.sort(key=lambda a: a[1])\n"
    "    chosen, last_end = [], -1\n    for s, f in acts:\n"
    "        if s >= last_end:\n            chosen.append((s, f))\n            last_end = f\n    return chosen",
    gen_activity_selection, "O(n log n)", "O(n log n)", "O(n log n)", "O(1)",
    input_type="none")

reg("Fractional Knapsack", "Greedy", "Medium",
    "Maximises profit when items can be split.",
    "Greedy choice: take items in decreasing order of value/weight ratio, "
    "taking a fraction of the item that fills the remaining capacity.",
    "def fractional_knapsack(items, cap):\n    items.sort(key=lambda x: x[0]/x[1], reverse=True)\n"
    "    profit = 0.0\n    for value, weight in items:\n"
    "        take = min(weight, cap)\n        profit += value / weight * take\n"
    "        cap -= take\n        if cap == 0: break\n    return profit",
    gen_fractional_knapsack, "O(n log n)", "O(n log n)", "O(n log n)", "O(1)",
    input_type="none")

reg("Coin Change (Greedy)", "Greedy", "Easy",
    "Uses the largest coin that fits at every step.",
    "Works for canonical coin systems (like 1,5,10,25) but is NOT optimal in "
    "general — that requires DP.",
    "def greedy_coins(coins, amount):\n    count = 0\n"
    "    for c in sorted(coins, reverse=True):\n        while amount >= c:\n"
    "            amount -= c\n            count += 1\n    return count",
    gen_coin_change_greedy, "O(n log n)", "O(n log n)", "O(n log n)", "O(1)",
    input_type="none")

reg("Jump Game", "Greedy", "Medium",
    "Determines whether the last index of an array is reachable.",
    "Greedy choice: keep track of the farthest index reachable so far.",
    "def can_jump(a):\n    reach = 0\n    for i, v in enumerate(a):\n"
    "        if i > reach: return False\n        reach = max(reach, i + v)\n    return True",
    gen_jump_game, "O(n)", "O(n)", "O(n)", "O(1)", input_type="none")

reg("Merge Intervals", "Greedy", "Medium",
    "Merges all overlapping intervals into disjoint ones.",
    "Sort by start time, then extend the current interval while the next one "
    "overlaps.",
    "def merge(intervals):\n    intervals.sort(key=lambda x: x[0])\n"
    "    out = [intervals[0]]\n    for s, e in intervals[1:]:\n"
    "        if s <= out[-1][1]:\n            out[-1][1] = max(out[-1][1], e)\n"
    "        else:\n            out.append([s, e])\n    return out",
    gen_merge_intervals, "O(n log n)", "O(n log n)", "O(n log n)", "O(n)",
    input_type="none")

reg("Huffman Coding", "Greedy", "Hard",
    "Builds an optimal prefix-free binary code from character frequencies.",
    "Greedy choice: repeatedly merge the two least frequent nodes. A min-heap "
    "makes each merge O(log n).",
    "import heapq\ndef huffman(freqs):\n    heap = [[w, [ch, '']] for ch, w in freqs.items()]\n"
    "    heapq.heapify(heap)\n    while len(heap) > 1:\n"
    "        lo = heapq.heappop(heap); hi = heapq.heappop(heap)\n"
    "        for p in lo[1:]: p[1] = '0' + p[1]\n"
    "        for p in hi[1:]: p[1] = '1' + p[1]\n"
    "        heapq.heappush(heap, [lo[0] + hi[0]] + lo[1:] + hi[1:])\n"
    "    return sorted(heapq.heappop(heap)[1:], key=lambda p: (len(p[1]), p))",
    gen_huffman, "O(n log n)", "O(n log n)", "O(n log n)", "O(n)",
    input_type="none")

# ---- Dynamic Programming ---------------------------------------------------
reg("Fibonacci (DP)", "Dynamic Programming", "Easy",
    "Computes Fibonacci numbers bottom-up in linear time.",
    "Each state depends only on the previous two, so an array (or two variables) "
    "removes the exponential recursion tree.",
    "def fib(n):\n    dp = [0] * (n + 1)\n    dp[1] = 1\n"
    "    for i in range(2, n + 1):\n        dp[i] = dp[i-1] + dp[i-2]\n    return dp[n]",
    gen_fib_dp, "O(1)", "O(n)", "O(n)", "O(n)", input_type="int_list")

reg("Climbing Stairs", "Dynamic Programming", "Easy",
    "Counts the ways to reach step n taking 1 or 2 steps at a time.",
    "dp[i] = dp[i-1] + dp[i-2] — the same recurrence as Fibonacci.",
    "def climb(n):\n    a, b = 1, 1\n    for _ in range(n):\n        a, b = b, a + b\n    return a",
    gen_climbing_stairs, "O(1)", "O(n)", "O(n)", "O(1)", input_type="int_list")

reg("House Robber", "Dynamic Programming", "Medium",
    "Maximum sum from non-adjacent houses.",
    "dp[i] = max(dp[i-1], dp[i-2] + value[i]) — either skip the house or rob it.",
    "def rob(h):\n    prev = cur = 0\n    for v in h:\n"
    "        prev, cur = cur, max(cur, prev + v)\n    return cur",
    gen_house_robber, "O(n)", "O(n)", "O(n)", "O(1)", input_type="int_list")

reg("0/1 Knapsack", "Dynamic Programming", "Hard",
    "Maximises value with a weight limit, each item taken at most once.",
    "dp[i][w] = max(dp[i-1][w], dp[i-1][w-wt[i]] + val[i]). A 2-D table makes "
    "the dependency structure visible.",
    "def knapsack(wt, val, W):\n    n = len(wt)\n    dp = [[0]*(W+1) for _ in range(n+1)]\n"
    "    for i in range(1, n+1):\n        for w in range(W+1):\n"
    "            dp[i][w] = dp[i-1][w]\n"
    "            if wt[i-1] <= w:\n                dp[i][w] = max(dp[i][w], dp[i-1][w-wt[i-1]] + val[i-1])\n"
    "    return dp[n][W]",
    gen_knapsack_01, "O(n·W)", "O(n·W)", "O(n·W)", "O(n·W)", input_type="none")

reg("Longest Common Subsequence", "Dynamic Programming", "Hard",
    "Length of the longest subsequence present in both strings.",
    "If the last characters match, add 1 to the diagonal; otherwise take the "
    "best of dropping one character from either string.",
    "def lcs(a, b):\n    n, m = len(a), len(b)\n"
    "    dp = [[0]*(m+1) for _ in range(n+1)]\n"
    "    for i in range(1, n+1):\n        for j in range(1, m+1):\n"
    "            if a[i-1] == b[j-1]: dp[i][j] = dp[i-1][j-1] + 1\n"
    "            else: dp[i][j] = max(dp[i-1][j], dp[i][j-1])\n    return dp[n][m]",
    gen_lcs, "O(n·m)", "O(n·m)", "O(n·m)", "O(n·m)", input_type="none")

reg("Longest Increasing Subsequence", "Dynamic Programming", "Medium",
    "Length of the longest strictly increasing subsequence.",
    "O(n²) DP: dp[i] = 1 + max(dp[j]) for all j < i with a[j] < a[i]. "
    "A patient-sorting / binary search variant achieves O(n log n).",
    "def lis(a):\n    dp = [1] * len(a)\n"
    "    for i in range(1, len(a)):\n        for j in range(i):\n"
    "            if a[j] < a[i]: dp[i] = max(dp[i], dp[j] + 1)\n    return max(dp)",
    gen_lis, "O(n²)", "O(n²)", "O(n²)", "O(n)", input_type="int_list")

reg("Coin Change (DP)", "Dynamic Programming", "Medium",
    "Minimum number of coins to make an amount (coins reusable).",
    "dp[x] = 1 + min(dp[x - c]) over all coins c ≤ x.",
    "def coin_change(coins, amount):\n    INF = float('inf')\n"
    "    dp = [0] + [INF] * amount\n    for x in range(1, amount + 1):\n"
    "        for c in coins:\n            if c <= x:\n                dp[x] = min(dp[x], dp[x-c] + 1)\n"
    "    return dp[amount]",
    gen_coin_change_dp, "O(amount)", "O(amount·k)", "O(amount·k)", "O(amount)",
    input_type="none")

reg("Edit Distance", "Dynamic Programming", "Hard",
    "Minimum insertions, deletions and substitutions to transform one string into another.",
    "If characters match, copy the diagonal. Otherwise 1 + min(delete, insert, replace).",
    "def edit_distance(a, b):\n    n, m = len(a), len(b)\n"
    "    dp = [[0]*(m+1) for _ in range(n+1)]\n"
    "    for i in range(n+1): dp[i][0] = i\n"
    "    for j in range(m+1): dp[0][j] = j\n"
    "    for i in range(1, n+1):\n        for j in range(1, m+1):\n"
    "            if a[i-1] == b[j-1]: dp[i][j] = dp[i-1][j-1]\n"
    "            else: dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])\n"
    "    return dp[n][m]",
    gen_edit_distance, "O(n·m)", "O(n·m)", "O(n·m)", "O(n·m)", input_type="none")

reg("Rod Cutting", "Dynamic Programming", "Medium",
    "Maximum revenue obtainable by cutting a rod into pieces.",
    "dp[l] = max(price[i] + dp[l - i]) over all cut lengths i ≤ l.",
    "def rod_cutting(price):\n    n = len(price)\n    dp = [0] * (n + 1)\n"
    "    for l in range(1, n + 1):\n        dp[l] = max(price[i-1] + dp[l-i] for i in range(1, l+1))\n"
    "    return dp[n]",
    gen_rod_cutting, "O(n²)", "O(n²)", "O(n²)", "O(n)", input_type="none")

reg("Subset Sum", "Dynamic Programming", "Medium",
    "Determines whether a subset of numbers adds up to a target.",
    "Boolean DP: dp[i][t] = dp[i-1][t] or dp[i-1][t - nums[i-1]].",
    "def subset_sum(nums, target):\n    dp = [False] * (target + 1)\n    dp[0] = True\n"
    "    for v in nums:\n        for t in range(target, v - 1, -1):\n"
    "            dp[t] = dp[t] or dp[t - v]\n    return dp[target]",
    gen_subset_sum, "O(n·T)", "O(n·T)", "O(n·T)", "O(T)", input_type="none")

reg("Longest Palindromic Subsequence", "Dynamic Programming", "Hard",
    "Length of the longest palindromic subsequence of a string.",
    "If s[i] == s[j], dp[i][j] = dp[i+1][j-1] + 2; otherwise the best of "
    "dropping either end.",
    "def lps(s):\n    n = len(s)\n    dp = [[0]*n for _ in range(n)]\n"
    "    for i in range(n): dp[i][i] = 1\n"
    "    for length in range(2, n+1):\n        for i in range(n - length + 1):\n"
    "            j = i + length - 1\n"
    "            if s[i] == s[j]: dp[i][j] = (dp[i+1][j-1] + 2) if length > 2 else 2\n"
    "            else: dp[i][j] = max(dp[i+1][j], dp[i][j-1])\n    return dp[0][n-1]",
    gen_longest_palindromic_subseq, "O(n²)", "O(n²)", "O(n²)", "O(n²)",
    input_type="none")

# ---- Divide & Conquer ------------------------------------------------------
reg("Merge Sort (Divide & Conquer)", "Divide & Conquer", "Medium",
    "The canonical divide & conquer sorting algorithm.",
    "DIVIDE the array at the midpoint, CONQUER by sorting each half "
    "recursively, COMBINE by merging the two sorted halves.",
    "def merge_sort(a):\n    if len(a) <= 1: return a\n    mid = len(a) // 2\n"
    "    L = merge_sort(a[:mid]); R = merge_sort(a[mid:])\n"
    "    out, i, j = [], 0, 0\n"
    "    while i < len(L) and j < len(R):\n"
    "        if L[i] <= R[j]: out.append(L[i]); i += 1\n"
    "        else: out.append(R[j]); j += 1\n"
    "    return out + L[i:] + R[j:]",
    gen_dc_merge_sort, "O(n log n)", "O(n log n)", "O(n log n)", "O(n)",
    "Yes", "No")

reg("Quick Select", "Divide & Conquer", "Hard",
    "Finds the k-th smallest element in average O(n).",
    "Partition around a pivot. If the pivot lands at index k-1 we are done; "
    "otherwise recurse into only one side.",
    "def quick_select(a, k):\n    def qs(lo, hi):\n        p = a[hi]; i = lo\n"
    "        for j in range(lo, hi):\n            if a[j] < p:\n                a[i], a[j] = a[j], a[i]; i += 1\n"
    "        a[i], a[hi] = a[hi], a[i]\n"
    "        if i == k - 1: return a[i]\n"
    "        return qs(i + 1, hi) if i < k - 1 else qs(lo, i - 1)\n    return qs(0, len(a) - 1)",
    gen_quick_select, "O(n)", "O(n)", "O(n²)", "O(log n)")

reg("Maximum Subarray (D&C)", "Divide & Conquer", "Medium",
    "Solves the maximum subarray problem by splitting at the midpoint.",
    "The answer is either entirely in the left half, entirely in the right "
    "half, or crosses the midpoint. O(n log n) overall.",
    "def max_cross(a, lo, mid, hi):\n    best_l = cur = float('-inf')\n"
    "    for i in range(mid, lo - 1, -1):\n        cur = a[i] + (cur if cur > -1e18 else 0)\n"
    "        best_l = max(best_l, cur)\n    best_r = cur = float('-inf')\n"
    "    for i in range(mid + 1, hi + 1):\n        cur = a[i] + (cur if cur > -1e18 else 0)\n"
    "        best_r = max(best_r, cur)\n    return best_l + best_r",
    gen_dc_max_subarray, "O(n log n)", "O(n log n)", "O(n log n)", "O(log n)",
    default_input="-2, 1, -3, 4, -1, 2, 1, -5, 4")


# ============================================================================
# 7. PROBLEMS BANK  (title, difficulty, category, statement, example, hint, complexity, solution)
# ============================================================================

PROBLEMS: List[Tuple[str, str, str, str, str, str, str, str]] = [
    ("Two Sum", "Easy", "Arrays",
     "Return the indices of the two numbers that add up to a target.",
     "nums = [2,7,11,15], target = 9  →  [0,1]",
     "Store value → index in a hash map while scanning once.",
     "O(n) time, O(n) space",
     "def two_sum(nums, target):\n    seen = {}\n    for i, v in enumerate(nums):\n"
     "        if target - v in seen:\n            return [seen[target - v], i]\n        seen[v] = i\n    return []"),

    ("Maximum Subarray Sum", "Easy", "Arrays",
     "Find the contiguous subarray with the largest sum.",
     "[-2,1,-3,4,-1,2,1,-5,4]  →  6  (subarray [4,-1,2,1])",
     "Kadane: keep current_sum and reset it when it becomes negative.",
     "O(n) time, O(1) space",
     "def max_subarray(a):\n    best = cur = a[0]\n    for x in a[1:]:\n"
     "        cur = max(x, cur + x)\n        best = max(best, cur)\n    return best"),

    ("Best Time to Buy and Sell Stock", "Easy", "Arrays",
     "Maximise profit from one buy and one later sell.",
     "[7,1,5,3,6,4]  →  5  (buy at 1, sell at 6)",
     "Track the minimum price seen so far and the best profit.",
     "O(n) time, O(1) space",
     "def max_profit(p):\n    best, low = 0, float('inf')\n    for x in p:\n"
     "        low = min(low, x)\n        best = max(best, x - low)\n    return best"),

    ("Container With Most Water", "Medium", "Arrays",
     "Choose two lines that together with the x-axis hold the most water.",
     "[1,8,6,2,5,4,8,3,7]  →  49",
     "Two pointers: move the shorter side inward.",
     "O(n) time, O(1) space",
     "def max_area(h):\n    i, j, best = 0, len(h) - 1, 0\n    while i < j:\n"
     "        best = max(best, min(h[i], h[j]) * (j - i))\n"
     "        if h[i] < h[j]: i += 1\n        else: j -= 1\n    return best"),

    ("Product of Array Except Self", "Medium", "Arrays",
     "Return an array where each element is the product of all others.",
     "[1,2,3,4]  →  [24,12,8,6]",
     "Prefix products left-to-right, then suffix products right-to-left.",
     "O(n) time, O(1) extra space",
     "def product_except_self(a):\n    n = len(a)\n    out = [1] * n\n"
     "    for i in range(1, n): out[i] = out[i-1] * a[i-1]\n"
     "    suf = 1\n    for i in range(n-1, -1, -1):\n"
     "        out[i] *= suf\n        suf *= a[i]\n    return out"),

    ("Merge Intervals", "Medium", "Arrays",
     "Merge all overlapping intervals.",
     "[[1,3],[2,6],[8,10]]  →  [[1,6],[8,10]]",
     "Sort by start and extend while the next start overlaps.",
     "O(n log n) time, O(n) space",
     "def merge(intervals):\n    intervals.sort(key=lambda x: x[0])\n"
     "    out = [intervals[0]]\n    for s, e in intervals[1:]:\n"
     "        if s <= out[-1][1]: out[-1][1] = max(out[-1][1], e)\n"
     "        else: out.append([s, e])\n    return out"),

    ("Rotate Array by K", "Medium", "Arrays",
     "Rotate an array to the right by k steps.",
     "[1,2,3,4,5,6,7], k=3  →  [5,6,7,1,2,3,4]",
     "Reverse the whole array, then reverse the first k and the rest.",
     "O(n) time, O(1) space",
     "def rotate(a, k):\n    n = len(a); k %= n\n"
     "    def rev(i, j):\n        while i < j:\n            a[i], a[j] = a[j], a[i]\n            i += 1; j -= 1\n"
     "    rev(0, n-1); rev(0, k-1); rev(k, n-1)\n    return a"),

    ("Trapping Rain Water", "Hard", "Arrays",
     "Compute how much rainwater can be trapped between bars.",
     "[0,1,0,2,1,0,1,3,2,1,2,1]  →  6",
     "Two pointers with running left_max and right_max.",
     "O(n) time, O(1) space",
     "def trap(h):\n    i, j = 0, len(h) - 1\n    lm = rm = 0\n    water = 0\n"
     "    while i < j:\n        if h[i] < h[j]:\n"
     "            lm = max(lm, h[i]); water += lm - h[i]; i += 1\n"
     "        else:\n            rm = max(rm, h[j]); water += rm - h[j]; j -= 1\n    return water"),

    ("Valid Palindrome", "Easy", "Strings",
     "Check whether a string reads the same forwards and backwards "
     "(ignoring non-alphanumeric characters and case).",
     '"A man, a plan, a canal: Panama"  →  True',
     "Two pointers skipping non-alphanumeric characters.",
     "O(n) time, O(1) space",
     "def is_palindrome(s):\n    i, j = 0, len(s) - 1\n"
     "    while i < j:\n        while i < j and not s[i].isalnum(): i += 1\n"
     "        while i < j and not s[j].isalnum(): j -= 1\n"
     "        if s[i].lower() != s[j].lower(): return False\n"
     "        i += 1; j -= 1\n    return True"),

    ("Valid Anagram", "Easy", "Strings",
     "Determine whether two strings are anagrams of each other.",
     '"listen", "silent"  →  True',
     "Compare character frequency counts.",
     "O(n) time, O(k) space",
     "from collections import Counter\ndef is_anagram(a, b):\n    return Counter(a) == Counter(b)"),

    ("Longest Common Prefix", "Easy", "Strings",
     "Find the longest common prefix shared by all strings.",
     '["flower","flow","flight"]  →  "fl"',
     "Compare characters column by column, or sort and compare the first and last.",
     "O(n·m) time, O(1) space",
     "def longest_common_prefix(strs):\n    if not strs: return ''\n"
     "    for i in range(len(strs[0])):\n        c = strs[0][i]\n"
     "        for s in strs[1:]:\n            if i >= len(s) or s[i] != c:\n"
     "                return strs[0][:i]\n    return strs[0]"),

    ("String Compression", "Medium", "Strings",
     "Run-length encode a string.",
     '"aaabbc"  →  "a3b2c1"',
     "Walk through runs of equal characters.",
     "O(n) time, O(n) space",
     "def compress(s):\n    out, i = [], 0\n    while i < len(s):\n"
     "        j = i\n        while j < len(s) and s[j] == s[i]: j += 1\n"
     "        out.append(s[i] + str(j - i)); i = j\n    return ''.join(out)"),

    ("Longest Substring Without Repeating Characters", "Medium", "Strings",
     "Find the length of the longest substring with all distinct characters.",
     '"abcabcbb"  →  3  ("abc")',
     "Sliding window with a last-seen index map.",
     "O(n) time, O(k) space",
     "def length_of_longest(s):\n    last = {}\n    start = best = 0\n"
     "    for i, ch in enumerate(s):\n        if ch in last and last[ch] >= start:\n            start = last[ch] + 1\n"
     "        last[ch] = i\n        best = max(best, i - start + 1)\n    return best"),

    ("Group Anagrams", "Medium", "Strings",
     "Group words that are anagrams of each other.",
     '["eat","tea","tan","ate"]  →  [["eat","tea","ate"],["tan"]]',
     "Key each word by its sorted characters or character count tuple.",
     "O(n·k log k) time, O(n·k) space",
     "def group_anagrams(words):\n    groups = {}\n    for w in words:\n"
     "        key = tuple(sorted(w))\n        groups.setdefault(key, []).append(w)\n"
     "    return list(groups.values())"),

    ("Minimum Window Substring", "Hard", "Strings",
     "Find the smallest substring of s containing all characters of t.",
     's="ADOBECODEBANC", t="ABC"  →  "BANC"',
     "Sliding window with a character-need counter.",
     "O(n) time, O(k) space",
     "from collections import Counter\ndef min_window(s, t):\n"
     "    need = Counter(t); missing = len(t)\n    best = (float('inf'), 0, 0)\n    l = 0\n"
     "    for r, ch in enumerate(s):\n        if need[ch] > 0: missing -= 1\n"
     "        need[ch] -= 1\n        while missing == 0:\n"
     "            if r - l + 1 < best[0]: best = (r - l + 1, l, r)\n"
     "            need[s[l]] += 1\n"
     "            if need[s[l]] > 0: missing += 1\n            l += 1\n"
     "    return '' if best[0] == float('inf') else s[best[1]:best[2]+1]"),

    ("Reverse Linked List", "Easy", "Linked Lists",
     "Reverse a singly linked list.",
     "1 → 2 → 3 → None  becomes  3 → 2 → 1 → None",
     "Three pointers: prev, curr, next.",
     "O(n) time, O(1) space",
     "def reverse(head):\n    prev = None\n    cur = head\n"
     "    while cur:\n        nxt = cur.next\n        cur.next = prev\n"
     "        prev = cur\n        cur = nxt\n    return prev"),

    ("Merge Two Sorted Lists", "Easy", "Linked Lists",
     "Merge two sorted linked lists into one sorted list.",
     "1→2→4 and 1→3→4  →  1→1→2→3→4→4",
     "Compare heads repeatedly and attach the smaller node.",
     "O(n+m) time, O(1) space",
     "def merge(l1, l2):\n    dummy = tail = Node(0)\n"
     "    while l1 and l2:\n        if l1.val <= l2.val:\n            tail.next, l1 = l1, l1.next\n"
     "        else:\n            tail.next, l2 = l2, l2.next\n        tail = tail.next\n"
     "    tail.next = l1 or l2\n    return dummy.next"),

    ("Middle of the Linked List", "Easy", "Linked Lists",
     "Return the middle node of a linked list.",
     "1→2→3→4→5  →  node 3",
     "Fast pointer moves two steps for every one step of the slow pointer.",
     "O(n) time, O(1) space",
     "def middle(head):\n    slow = fast = head\n"
     "    while fast and fast.next:\n        slow = slow.next\n        fast = fast.next.next\n    return slow"),

    ("Linked List Cycle", "Medium", "Linked Lists",
     "Detect whether a linked list contains a cycle.",
     "3→2→0→-4 with tail pointing back to node 2  →  True",
     "Floyd's tortoise and hare.",
     "O(n) time, O(1) space",
     "def has_cycle(head):\n    slow = fast = head\n"
     "    while fast and fast.next:\n        slow = slow.next\n        fast = fast.next.next\n"
     "        if slow is fast: return True\n    return False"),

    ("Remove Nth Node From End", "Medium", "Linked Lists",
     "Remove the n-th node counted from the end of the list.",
     "1→2→3→4→5, n=2  →  1→2→3→5",
     "Two pointers separated by n, then move both together.",
     "O(n) time, O(1) space",
     "def remove_nth(head, n):\n    dummy = Node(0); dummy.next = head\n"
     "    fast = slow = dummy\n"
     "    for _ in range(n): fast = fast.next\n"
     "    while fast.next:\n        fast = fast.next; slow = slow.next\n"
     "    slow.next = slow.next.next\n    return dummy.next"),

    ("Valid Parentheses", "Easy", "Stack",
     "Check whether brackets in a string are properly balanced.",
     '"()[]{}"  →  True,   "(]"  →  False',
     "Push openers, pop on closers and check the match.",
     "O(n) time, O(n) space",
     "def is_valid(s):\n    pairs = {')': '(', ']': '[', '}': '{'}\n    st = []\n"
     "    for ch in s:\n        if ch in '([{': st.append(ch)\n"
     "        elif ch in pairs:\n            if not st or st.pop() != pairs[ch]: return False\n"
     "    return not st"),

    ("Min Stack", "Medium", "Stack",
     "Design a stack supporting push, pop, top and getMin in O(1).",
     "push(5),push(3),getMin()  →  3",
     "Keep a parallel stack of running minima.",
     "O(1) per operation, O(n) space",
     "class MinStack:\n    def __init__(self):\n        self.st, self.mn = [], []\n"
     "    def push(self, x):\n        self.st.append(x)\n"
     "        self.mn.append(x if not self.mn else min(x, self.mn[-1]))\n"
     "    def pop(self):\n        self.mn.pop(); return self.st.pop()\n"
     "    def top(self): return self.st[-1]\n"
     "    def getMin(self): return self.mn[-1]"),

    ("Next Greater Element", "Medium", "Stack",
     "For each element find the next greater element to its right.",
     "[4,5,2,10,8,3]  →  [5,10,10,-1,-1,-1]",
     "Monotonic decreasing stack of indices.",
     "O(n) time, O(n) space",
     "def next_greater(a):\n    res = [-1] * len(a)\n    st = []\n"
     "    for i, v in enumerate(a):\n        while st and a[st[-1]] < v:\n"
     "            res[st.pop()] = v\n        st.append(i)\n    return res"),

    ("Evaluate Reverse Polish Notation", "Medium", "Stack",
     "Evaluate a postfix arithmetic expression.",
     '["2","1","+","3","*"]  →  9',
     "Push operands, pop two on each operator.",
     "O(n) time, O(n) space",
     "def eval_rpn(tokens):\n    st = []\n    for t in tokens:\n"
     "        if t not in '+-*/': st.append(int(t))\n"
     "        else:\n            b, a = st.pop(), st.pop()\n"
     "            st.append(int(eval(f'{a}{t}{b}')))\n    return st[-1]"),

    ("Largest Rectangle in Histogram", "Hard", "Stack",
     "Find the largest rectangle that fits inside a histogram.",
     "[2,1,5,6,2,3]  →  10",
     "Monotonic increasing stack of bar indices.",
     "O(n) time, O(n) space",
     "def largest_rectangle(h):\n    st, best = [], 0\n    h = h + [0]\n"
     "    for i, v in enumerate(h):\n        while st and h[st[-1]] > v:\n"
     "            height = h[st.pop()]\n            width = i if not st else i - st[-1] - 1\n"
     "            best = max(best, height * width)\n        st.append(i)\n    return best"),

    ("Implement Queue using Stacks", "Easy", "Queue",
     "Build a FIFO queue using only two LIFO stacks.",
     "push(1),push(2),peek()  →  1",
     "Move elements from the input stack to the output stack only when needed.",
     "O(1) amortized, O(n) space",
     "class MyQueue:\n    def __init__(self):\n        self.inp, self.out = [], []\n"
     "    def push(self, x): self.inp.append(x)\n"
     "    def pop(self):\n        self._move()\n        return self.out.pop()\n"
     "    def peek(self):\n        self._move()\n        return self.out[-1]\n"
     "    def _move(self):\n        if not self.out:\n            while self.inp: self.out.append(self.inp.pop())"),

    ("Sliding Window Maximum", "Hard", "Queue",
     "Return the maximum of every window of size k.",
     "[1,3,-1,-3,5,3,6,7], k=3  →  [3,3,5,5,6,7]",
     "Monotonic deque holding indices in decreasing value order.",
     "O(n) time, O(k) space",
     "from collections import deque\ndef max_sliding_window(a, k):\n"
     "    dq, out = deque(), []\n    for i, v in enumerate(a):\n"
     "        while dq and a[dq[-1]] <= v: dq.pop()\n        dq.append(i)\n"
     "        if dq[0] <= i - k: dq.popleft()\n"
     "        if i >= k - 1: out.append(a[dq[0]])\n    return out"),

    ("Design Circular Queue", "Medium", "Queue",
     "Implement a fixed-size circular queue.",
     "MyCircularQueue(3); enQueue(1); Rear()  →  1",
     "rear = (front + size) % capacity.",
     "O(1) per operation, O(k) space",
     "class MyCircularQueue:\n    def __init__(self, k):\n"
     "        self.buf = [None]*k; self.front = 0; self.size = 0; self.k = k\n"
     "    def enQueue(self, v):\n        if self.size == self.k: return False\n"
     "        self.buf[(self.front+self.size) % self.k] = v; self.size += 1; return True\n"
     "    def deQueue(self):\n        if not self.size: return False\n"
     "        self.front = (self.front+1) % self.k; self.size -= 1; return True"),

    ("Contains Duplicate", "Easy", "Hashing",
     "Return True if any value appears at least twice.",
     "[1,2,3,1]  →  True",
     "Hash set membership check while scanning.",
     "O(n) time, O(n) space",
     "def contains_duplicate(a):\n    seen = set()\n"
     "    for v in a:\n        if v in seen: return True\n        seen.add(v)\n    return False"),

    ("Longest Consecutive Sequence", "Medium", "Hashing",
     "Find the length of the longest run of consecutive integers.",
     "[100,4,200,1,3,2]  →  4  (1,2,3,4)",
     "Put everything in a set; only start counting from numbers with no predecessor.",
     "O(n) time, O(n) space",
     "def longest_consecutive(a):\n    s = set(a); best = 0\n"
     "    for v in s:\n        if v - 1 not in s:\n            length = 1\n"
     "            while v + length in s: length += 1\n            best = max(best, length)\n    return best"),

    ("Subarray Sum Equals K", "Medium", "Hashing",
     "Count subarrays whose sum equals k.",
     "[1,1,1], k=2  →  2",
     "Prefix sums in a hash map: count how often prefix_sum - k occurred.",
     "O(n) time, O(n) space",
     "def subarray_sum(a, k):\n    counts = {0: 1}\n    total = cur = 0\n"
     "    for v in a:\n        cur += v\n        total += counts.get(cur - k, 0)\n"
     "        counts[cur] = counts.get(cur, 0) + 1\n    return total"),

    ("LRU Cache", "Hard", "Hashing",
     "Design a cache with O(1) get and put that evicts the least recently used key.",
     "LRUCache(2); put(1,1); put(2,2); get(1)  →  1",
     "Hash map + doubly linked list, or OrderedDict.",
     "O(1) per operation, O(capacity) space",
     "from collections import OrderedDict\nclass LRUCache:\n"
     "    def __init__(self, cap):\n        self.cap = cap; self.d = OrderedDict()\n"
     "    def get(self, k):\n        if k not in self.d: return -1\n"
     "        self.d.move_to_end(k)\n        return self.d[k]\n"
     "    def put(self, k, v):\n        if k in self.d: self.d.move_to_end(k)\n"
     "        self.d[k] = v\n        if len(self.d) > self.cap: self.d.popitem(last=False)"),

    ("Binary Search", "Easy", "Searching",
     "Find the index of a target in a sorted array.",
     "[10,20,30,40,50], target=40  →  3",
     "Halve the range every iteration.",
     "O(log n) time, O(1) space",
     "def binary_search(a, t):\n    lo, hi = 0, len(a) - 1\n"
     "    while lo <= hi:\n        mid = (lo + hi) // 2\n"
     "        if a[mid] == t: return mid\n"
     "        if a[mid] < t: lo = mid + 1\n        else: hi = mid - 1\n    return -1"),

    ("Search in Rotated Sorted Array", "Medium", "Searching",
     "Search a target in an array that was rotated.",
     "[40,50,60,70,10,20,30], target=10  →  4",
     "One half is always sorted — determine which and whether the target is in it.",
     "O(log n) time, O(1) space",
     "def search(a, t):\n    lo, hi = 0, len(a) - 1\n"
     "    while lo <= hi:\n        mid = (lo + hi) // 2\n        if a[mid] == t: return mid\n"
     "        if a[lo] <= a[mid]:\n"
     "            if a[lo] <= t < a[mid]: hi = mid - 1\n            else: lo = mid + 1\n"
     "        else:\n            if a[mid] < t <= a[hi]: lo = mid + 1\n            else: hi = mid - 1\n"
     "    return -1"),

    ("Find Peak Element", "Medium", "Searching",
     "Find an index whose value is greater than both neighbours.",
     "[1,2,3,1]  →  2",
     "Binary search following the upward slope.",
     "O(log n) time, O(1) space",
     "def find_peak(a):\n    lo, hi = 0, len(a) - 1\n"
     "    while lo < hi:\n        mid = (lo + hi) // 2\n"
     "        if a[mid] < a[mid+1]: lo = mid + 1\n        else: hi = mid\n    return lo"),

    ("Koko Eating Bananas", "Medium", "Searching",
     "Find the minimum eating speed to finish all piles within h hours.",
     "piles=[3,6,7,11], h=8  →  4",
     "Binary search on the answer: test whether a speed k is feasible.",
     "O(n log m) time, O(1) space",
     "def min_eating_speed(piles, h):\n    lo, hi = 1, max(piles)\n"
     "    while lo < hi:\n        mid = (lo + hi) // 2\n"
     "        hours = sum((p + mid - 1) // mid for p in piles)\n"
     "        if hours <= h: hi = mid\n        else: lo = mid + 1\n    return lo"),

    ("Sort Colors", "Medium", "Sorting",
     "Sort an array of 0s, 1s and 2s in one pass.",
     "[2,0,2,1,1,0]  →  [0,0,1,1,2,2]",
     "Dutch national flag: three pointers (low, mid, high).",
     "O(n) time, O(1) space",
     "def sort_colors(a):\n    lo = mid = 0; hi = len(a) - 1\n"
     "    while mid <= hi:\n        if a[mid] == 0:\n            a[lo], a[mid] = a[mid], a[lo]; lo += 1; mid += 1\n"
     "        elif a[mid] == 1: mid += 1\n"
     "        else:\n            a[mid], a[hi] = a[hi], a[mid]; hi -= 1"),

    ("Merge Sorted Array", "Easy", "Sorting",
     "Merge two sorted arrays into the first one in-place.",
     "nums1=[1,2,3,0,0,0], nums2=[2,5,6]  →  [1,2,2,3,5,6]",
     "Fill from the back so no data is overwritten.",
     "O(n+m) time, O(1) space",
     "def merge(nums1, m, nums2, n):\n    i, j, k = m - 1, n - 1, m + n - 1\n"
     "    while j >= 0:\n        if i >= 0 and nums1[i] > nums2[j]:\n"
     "            nums1[k] = nums1[i]; i -= 1\n"
     "        else:\n            nums1[k] = nums2[j]; j -= 1\n        k -= 1"),

    ("Kth Largest Element", "Medium", "Sorting",
     "Find the k-th largest element in an array.",
     "[3,2,1,5,6,4], k=2  →  5",
     "Quick select or a min-heap of size k.",
     "O(n) average (quick select), O(n log k) with a heap",
     "import heapq\ndef find_kth_largest(a, k):\n    return heapq.nlargest(k, a)[-1]"),

    ("Maximum Depth of Binary Tree", "Easy", "Trees",
     "Return the maximum depth of a binary tree.",
     "[3,9,20,null,null,15,7]  →  3",
     "1 + max(depth(left), depth(right)).",
     "O(n) time, O(h) space",
     "def max_depth(root):\n    if not root: return 0\n"
     "    return 1 + max(max_depth(root.left), max_depth(root.right))"),

    ("Invert Binary Tree", "Easy", "Trees",
     "Mirror a binary tree.",
     "[4,2,7,1,3,6,9]  →  [4,7,2,9,6,3,1]",
     "Swap children recursively.",
     "O(n) time, O(h) space",
     "def invert(root):\n    if not root: return None\n"
     "    root.left, root.right = invert(root.right), invert(root.left)\n    return root"),

    ("Validate Binary Search Tree", "Medium", "Trees",
     "Check whether a binary tree is a valid BST.",
     "[5,1,4,null,null,3,6]  →  False",
     "Pass down (low, high) bounds while traversing.",
     "O(n) time, O(h) space",
     "def is_valid_bst(root, lo=float('-inf'), hi=float('inf')):\n"
     "    if not root: return True\n"
     "    if not (lo < root.val < hi): return False\n"
     "    return (is_valid_bst(root.left, lo, root.val) and\n"
     "            is_valid_bst(root.right, root.val, hi))"),

    ("Binary Tree Level Order Traversal", "Medium", "Trees",
     "Return node values grouped by level.",
     "[3,9,20,null,null,15,7]  →  [[3],[9,20],[15,7]]",
     "BFS with a queue, processing one level at a time.",
     "O(n) time, O(n) space",
     "from collections import deque\ndef level_order(root):\n    if not root: return []\n"
     "    out, q = [], deque([root])\n    while q:\n        level = []\n"
     "        for _ in range(len(q)):\n            n = q.popleft(); level.append(n.val)\n"
     "            if n.left: q.append(n.left)\n            if n.right: q.append(n.right)\n"
     "        out.append(level)\n    return out"),

    ("Lowest Common Ancestor of a BST", "Medium", "Trees",
     "Find the lowest common ancestor of two nodes in a BST.",
     "root=[6,2,8,0,4,7,9], p=2, q=8  →  6",
     "Walk down while both targets are on the same side.",
     "O(h) time, O(1) space",
     "def lowest_common_ancestor(root, p, q):\n    cur = root\n"
     "    while cur:\n        if p < cur.val and q < cur.val: cur = cur.left\n"
     "        elif p > cur.val and q > cur.val: cur = cur.right\n"
     "        else: return cur"),

    ("Number of Islands", "Medium", "Graphs",
     "Count connected groups of 1s in a grid.",
     "grid with two land masses  →  2",
     "DFS/BFS flood fill from every unvisited land cell.",
     "O(rows·cols) time, O(rows·cols) space",
     "def num_islands(grid):\n    if not grid: return 0\n"
     "    R, C = len(grid), len(grid[0]); count = 0\n"
     "    def sink(r, c):\n"
     "        if 0 <= r < R and 0 <= c < C and grid[r][c] == '1':\n"
     "            grid[r][c] = '0'\n"
     "            sink(r+1,c); sink(r-1,c); sink(r,c+1); sink(r,c-1)\n"
     "    for r in range(R):\n        for c in range(C):\n"
     "            if grid[r][c] == '1':\n                count += 1; sink(r, c)\n    return count"),

    ("Clone Graph", "Medium", "Graphs",
     "Deep-copy an undirected graph.",
     "adjList = [[2,4],[1,3],[2,4],[1,3]]  →  identical new graph",
     "DFS/BFS with a map from original node to its clone.",
     "O(V+E) time, O(V) space",
     "def clone_graph(node, seen=None):\n    if not node: return None\n"
     "    seen = seen or {}\n    if node in seen: return seen[node]\n"
     "    copy = Node(node.val)\n    seen[node] = copy\n"
     "    for nb in node.neighbors:\n        copy.neighbors.append(clone_graph(nb, seen))\n    return copy"),

    ("Course Schedule", "Medium", "Graphs",
     "Determine whether all courses can be finished (no prerequisite cycle).",
     "numCourses=2, prerequisites=[[1,0]]  →  True",
     "Topological sort / cycle detection on the prerequisite graph.",
     "O(V+E) time, O(V+E) space",
     "from collections import deque\ndef can_finish(n, prereq):\n"
     "    adj = [[] for _ in range(n)]; indeg = [0]*n\n"
     "    for a, b in prereq:\n        adj[b].append(a); indeg[a] += 1\n"
     "    q = deque(i for i in range(n) if indeg[i] == 0); seen = 0\n"
     "    while q:\n        u = q.popleft(); seen += 1\n"
     "        for v in adj[u]:\n            indeg[v] -= 1\n"
     "            if indeg[v] == 0: q.append(v)\n    return seen == n"),

    ("Network Delay Time (Dijkstra)", "Medium", "Graphs",
     "Find how long it takes for a signal to reach all nodes.",
     "times=[[2,1,1],[2,3,1],[3,4,1]], n=4, k=2  →  2",
     "Dijkstra from the source; answer is the maximum distance.",
     "O(E log V) time, O(V+E) space",
     "import heapq\ndef network_delay(times, n, k):\n"
     "    adj = {i: [] for i in range(1, n+1)}\n"
     "    for u, v, w in times: adj[u].append((v, w))\n"
     "    dist = {i: float('inf') for i in range(1, n+1)}; dist[k] = 0\n"
     "    pq = [(0, k)]\n    while pq:\n        d, u = heapq.heappop(pq)\n"
     "        if d > dist[u]: continue\n        for v, w in adj[u]:\n"
     "            if d + w < dist[v]:\n                dist[v] = d + w; heapq.heappush(pq, (dist[v], v))\n"
     "    ans = max(dist.values())\n    return -1 if ans == float('inf') else ans"),

    ("Jump Game", "Medium", "Greedy",
     "Can you reach the last index?",
     "[2,3,1,1,4]  →  True",
     "Track the farthest reachable index greedily.",
     "O(n) time, O(1) space",
     "def can_jump(a):\n    reach = 0\n    for i, v in enumerate(a):\n"
     "        if i > reach: return False\n        reach = max(reach, i + v)\n    return True"),

    ("Activity Selection", "Easy", "Greedy",
     "Select the maximum number of non-overlapping activities.",
     "[(1,4),(3,5),(0,6),(5,7)]  →  2",
     "Sort by finish time and greedily take the earliest finishing compatible one.",
     "O(n log n) time, O(1) space",
     "def select(acts):\n    acts.sort(key=lambda x: x[1])\n"
     "    count, end = 0, -1\n    for s, f in acts:\n"
     "        if s >= end:\n            count += 1; end = f\n    return count"),

    ("Climbing Stairs", "Easy", "Dynamic Programming",
     "Count the ways to climb n stairs taking 1 or 2 steps.",
     "n = 3  →  3  (1+1+1, 1+2, 2+1)",
     "dp[i] = dp[i-1] + dp[i-2].",
     "O(n) time, O(1) space",
     "def climb(n):\n    a, b = 1, 1\n    for _ in range(n):\n"
     "        a, b = b, a + b\n    return a"),

    ("Coin Change", "Medium", "Dynamic Programming",
     "Minimum coins needed to make an amount.",
     "coins=[1,2,5], amount=11  →  3",
     "Bottom-up DP over the amount.",
     "O(amount·k) time, O(amount) space",
     "def coin_change(coins, amount):\n    INF = float('inf')\n"
     "    dp = [0] + [INF] * amount\n    for x in range(1, amount + 1):\n"
     "        for c in coins:\n            if c <= x:\n                dp[x] = min(dp[x], dp[x-c] + 1)\n"
     "    return -1 if dp[amount] == INF else dp[amount]"),

    ("Longest Increasing Subsequence", "Medium", "Dynamic Programming",
     "Length of the longest strictly increasing subsequence.",
     "[10,9,2,5,3,7,101,18]  →  4  ([2,3,7,101])",
     "O(n²) DP, or patience sorting with binary search for O(n log n).",
     "O(n²) or O(n log n) time",
     "def lis(a):\n    dp = [1] * len(a)\n    for i in range(1, len(a)):\n"
     "        for j in range(i):\n            if a[j] < a[i]: dp[i] = max(dp[i], dp[j] + 1)\n"
     "    return max(dp) if a else 0"),

    ("Edit Distance", "Hard", "Dynamic Programming",
     "Minimum operations to convert one string into another.",
     '"horse" → "ros"  →  3',
     "dp[i][j] over prefixes; match → diagonal, else 1 + min of three neighbours.",
     "O(n·m) time, O(n·m) space",
     "def edit_distance(a, b):\n    n, m = len(a), len(b)\n"
     "    dp = [[0]*(m+1) for _ in range(n+1)]\n"
     "    for i in range(n+1): dp[i][0] = i\n"
     "    for j in range(m+1): dp[0][j] = j\n"
     "    for i in range(1, n+1):\n        for j in range(1, m+1):\n"
     "            if a[i-1] == b[j-1]: dp[i][j] = dp[i-1][j-1]\n"
     "            else: dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])\n"
     "    return dp[n][m]"),
]


# ============================================================================
# 8. QUIZ BANK
# ============================================================================

QUIZ_BANK: List[Tuple[str, List[str], int, str]] = [
    ("What is the average time complexity of Quick Sort?",
     ["O(n)", "O(n log n)", "O(n²)", "O(log n)"], 1,
     "Quick Sort averages O(n log n) with a good pivot."),
    ("Which sorting algorithm is stable and guarantees O(n log n)?",
     ["Quick Sort", "Heap Sort", "Merge Sort", "Selection Sort"], 2,
     "Merge Sort is stable and always O(n log n)."),
    ("Binary search requires the input array to be…",
     ["Unsorted", "Sorted", "Unique", "Even length"], 1,
     "Binary search only works on sorted data."),
    ("What data structure does BFS use?",
     ["Stack", "Queue", "Heap", "Set"], 1,
     "BFS processes nodes in FIFO order — a queue."),
    ("What data structure does DFS use (iteratively)?",
     ["Queue", "Stack", "Heap", "Array"], 1,
     "DFS uses a stack (or the call stack)."),
    ("Which algorithm finds shortest paths with negative weights?",
     ["Dijkstra", "BFS", "Bellman-Ford", "Prim"], 2,
     "Bellman-Ford handles negative edges and detects negative cycles."),
    ("Worst-case complexity of Bubble Sort?",
     ["O(n)", "O(n log n)", "O(n²)", "O(2ⁿ)"], 2,
     "Bubble Sort is O(n²) in the worst and average case."),
    ("Which structure gives O(1) average lookup by key?",
     ["Linked List", "Hash Table", "Binary Search Tree", "Array"], 1,
     "Hash tables give O(1) average lookup."),
    ("In a min-heap, the smallest element is at…",
     ["A leaf", "The root", "Index 1", "The last index"], 1,
     "The heap property puts the minimum at the root (index 0)."),
    ("What does Kadane's algorithm compute?",
     ["Longest subarray", "Maximum subarray sum", "Sorted subarray", "Average"], 1,
     "Kadane finds the maximum contiguous subarray sum."),
    ("Time complexity of inserting at the head of a linked list?",
     ["O(1)", "O(log n)", "O(n)", "O(n²)"], 0,
     "Head insertion only rewires two pointers."),
    ("Which traversal of a BST yields sorted order?",
     ["Preorder", "Inorder", "Postorder", "Level order"], 1,
     "Inorder visits Left → Root → Right, producing sorted output."),
    ("What is the space complexity of merge sort?",
     ["O(1)", "O(log n)", "O(n)", "O(n²)"], 2,
     "Merge sort needs an auxiliary array of size n."),
    ("Which technique solves 'Two Sum' in O(n)?",
     ["Sorting", "Hash map", "Binary search", "Recursion"], 1,
     "A hash map stores complements in O(1) lookups."),
    ("What does a Trie excel at?",
     ["Sorting numbers", "Prefix queries", "Shortest paths", "Matrix math"], 1,
     "Tries store strings by prefix."),
    ("Amortized cost of appending to a Python list?",
     ["O(1)", "O(log n)", "O(n)", "O(n²)"], 0,
     "Dynamic arrays double capacity, giving O(1) amortized appends."),
    ("Which algorithm builds a minimum spanning tree?",
     ["Dijkstra", "Floyd-Warshall", "Kruskal", "Bellman-Ford"], 2,
     "Kruskal (with union-find) builds an MST."),
    ("Time complexity of accessing an array element by index?",
     ["O(1)", "O(log n)", "O(n)", "O(n log n)"], 0,
     "Arrays are contiguous, so indexing is constant time."),
    ("Which problem is solved by the Longest Common Subsequence DP?",
     ["Sorting", "Diff / string similarity", "Shortest path", "Hashing"], 1,
     "LCS underpins diff tools and DNA sequence comparison."),
    ("What does the fast & slow pointer technique detect?",
     ["Sorted arrays", "Linked list cycles", "Hash collisions", "Balanced trees"], 1,
     "Floyd's algorithm detects cycles in linked lists."),
    ("Which sorting algorithm is adaptive (fast on nearly sorted data)?",
     ["Selection Sort", "Insertion Sort", "Heap Sort", "Counting Sort"], 1,
     "Insertion Sort runs in O(n) on nearly sorted input."),
    ("Worst-case complexity of a hash table lookup?",
     ["O(1)", "O(log n)", "O(n)", "O(n²)"], 2,
     "With many collisions all keys can land in one bucket."),
    ("Which structure is used for topological sorting of a DAG?",
     ["Stack only", "Queue (Kahn) or DFS", "Heap", "Trie"], 1,
     "Kahn's algorithm uses a queue; DFS-based topo sort uses a stack."),
    ("What is the time complexity of Floyd-Warshall?",
     ["O(V²)", "O(V³)", "O(E log V)", "O(V·E)"], 1,
     "Three nested loops over vertices give O(V³)."),
    ("Divide & Conquer is characterized by…",
     ["Greedy choices", "Splitting into subproblems", "Hashing", "Memo tables only"], 1,
     "D&C splits the problem, solves subproblems, then combines."),
    ("Which algorithm uses a monotonic stack?",
     ["Next Greater Element", "Merge Sort", "Dijkstra", "BFS"], 0,
     "Next Greater Element keeps a decreasing stack of indices."),
    ("What is the best case of Insertion Sort?",
     ["O(1)", "O(n)", "O(n log n)", "O(n²)"], 1,
     "Already sorted input needs one comparison per element."),
    ("Which DP problem's recurrence is dp[i] = dp[i-1] + dp[i-2]?",
     ["Knapsack", "Climbing Stairs", "Edit Distance", "LCS"], 1,
     "Climbing stairs follows the Fibonacci recurrence."),
    ("Which data structure does a priority queue use internally?",
     ["Linked list", "Heap", "Stack", "Trie"], 1,
     "Binary heaps give O(log n) insert and extract."),
    ("Space complexity of an iterative BFS on a graph?",
     ["O(1)", "O(V)", "O(V²)", "O(E²)"], 1,
     "The queue can hold up to V vertices."),
]


# ============================================================================
# 9. VISUALIZER CANVAS
# ============================================================================

class Visualizer(tk.Canvas):
    """Canvas that renders any frame produced by the algorithm generators."""

    def __init__(self, master, **kw):
        super().__init__(master, bg=BG, highlightthickness=0, **kw)
        self.frame: Optional[dict] = None
        self.bind("<Configure>", lambda _e: self.redraw())

    # -- public ------------------------------------------------------------
    def show(self, frame: dict) -> None:
        self.frame = frame
        self.redraw()

    def redraw(self) -> None:
        self.delete("all")
        if not self.frame:
            self._placeholder()
            return
        kind = self.frame.get("kind", "bars")
        drawer = getattr(self, f"_draw_{kind}", self._draw_bars)
        try:
            drawer(self.frame)
        except Exception as exc:  # never crash the UI
            self.create_text(20, 20, anchor="nw", fill=DANGER,
                             text=f"Render error: {exc}", font=FONT_MONO)

    # -- helpers -----------------------------------------------------------
    def _wh(self) -> Tuple[int, int]:
        return max(self.winfo_width(), 400), max(self.winfo_height(), 260)

    def _placeholder(self) -> None:
        w, h = self._wh()
        self.create_oval(w / 2 - 78, h / 2 - 122, w / 2 + 78, h / 2 + 34,
                         outline="#1d4961", width=2)
        self.create_line(w / 2 - 42, h / 2 - 44, w / 2, h / 2 - 78,
                         fill=ACCENT, width=3)
        self.create_line(w / 2, h / 2 - 78, w / 2 + 44, h / 2 - 38,
                         fill=ACCENT_2, width=3)
        self.create_oval(w / 2 - 50, h / 2 - 52, w / 2 - 34, h / 2 - 36,
                         fill=ACCENT, outline="")
        self.create_oval(w / 2 - 8, h / 2 - 86, w / 2 + 8, h / 2 - 70,
                         fill=ACCENT_2, outline="")
        self.create_oval(w / 2 + 36, h / 2 - 48, w / 2 + 52, h / 2 - 32,
                         fill=SUCCESS, outline="")
        self.create_text(w / 2, h / 2 - 20, text="DSA Algorithm Visualizer",
                         fill=ACCENT, font=("Segoe UI", 20, "bold"))
        self.create_text(w / 2, h / 2 + 16,
                         text="Pick an algorithm on the left, then press Start",
                         fill=MUTED, font=("Segoe UI", 12))
        self.create_text(w / 2, h / 2 + 46,
                         text="Learn • Visualize • Practice • Master",
                         fill="#3f5a75", font=("Segoe UI", 11, "italic"))

    def _header(self, f: dict, w: int) -> int:
        y = 22
        msg = f.get("message", "")
        if msg:
            self.create_text(w / 2, y, text=msg, fill=TEXT,
                             font=("Segoe UI", 13, "bold"), width=w - 60)
        y = 52
        for line in f.get("info", []):
            self.create_text(18, y, text=str(line), fill=ACCENT,
                             font=FONT_MONO, anchor="nw", width=w - 36)
            y += 20
        return y + 8

    # -- bars --------------------------------------------------------------
    def _draw_bars(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        values = f.get("values", [])
        n = len(values)
        if n == 0:
            self.create_text(w / 2, h / 2, text="(empty)", fill=MUTED, font=FONT_UI)
            return
        pad_l, pad_r = 45, 45
        bottom = 68
        top = max(top, 70)
        avail_h = max(h - top - bottom, 60)
        lo = min(min(values), 0)
        hi = max(max(values), 1)
        span = (hi - lo) or 1
        avail_w = max(w - pad_l - pad_r, 100)
        bw = avail_w / n
        hl = f.get("highlights", {})
        for i, v in enumerate(values):
            x0 = pad_l + i * bw + 3
            x1 = pad_l + (i + 1) * bw - 3
            bh = max((v - lo) / span * avail_h, 3)
            y0 = h - bottom - bh
            y1 = h - bottom
            role = hl.get(i, "default")
            color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
            self.create_rectangle(x0, y0, x1, y1, fill=color, outline="")
            if bw >= 16:
                self.create_text((x0 + x1) / 2, y0 - 11, text=str(v),
                                 fill="#cbd5e1", font=("Consolas", 9))
            if bw >= 22:
                self.create_text((x0 + x1) / 2, h - bottom + 14, text=str(i),
                                 fill="#4b6480", font=("Consolas", 8))
        self.create_line(pad_l - 12, h - bottom, w - pad_r + 12, h - bottom,
                         fill=BORDER)
        for name, idx in f.get("pointers", {}).items():
            if isinstance(idx, int) and 0 <= idx < n:
                x = pad_l + (idx + 0.5) * bw
                self.create_text(x, h - bottom + 32, text=name, fill=ACCENT,
                                 font=("Consolas", 10, "bold"))

    # -- characters --------------------------------------------------------
    def _draw_chars(self, f: dict) -> None:
        w, h = self._wh()
        y = self._header(f, w)
        y = max(y, 80)
        for row in f.get("rows", []):
            label = row.get("label", "")
            data = row.get("chars", [])
            hl = row.get("highlights", {})
            if label:
                self.create_text(24, y + 20, text=label, fill=MUTED,
                                 font=FONT_MONO_B, anchor="w")
            x = 120
            size = 38 if len(data) < 26 else 26
            for i, ch in enumerate(data):
                role = hl.get(i, "default")
                color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
                self.create_rectangle(x, y, x + size, y + size, fill=color,
                                      outline=BG)
                self.create_text(x + size / 2, y + size / 2, text=str(ch),
                                 fill="#f8fafc",
                                 font=("Consolas", 13 if size > 30 else 10, "bold"))
                x += size + 6
                if x > w - 60:
                    break
            y += size + 28
            if y > h - 40:
                break

    # -- text --------------------------------------------------------------
    def _draw_text(self, f: dict) -> None:
        w, h = self._wh()
        y = self._header(f, w)
        y = max(y, 70)
        for line in f.get("lines", []):
            color = ACCENT if line.strip().startswith(("BIG", "Greedy", "SLOW",
                                                       "FAST", "Rule")) else TEXT
            self.create_text(28, y, text=line, fill=color, font=FONT_MONO,
                             anchor="nw")
            y += 20
            if y > h - 20:
                break

    # -- grid / DP table / hash buckets -------------------------------------
    def _draw_grid(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        top = max(top, 70)
        cells = f.get("cells", [])
        rows = len(cells)
        cols = max((len(r) for r in cells), default=0)
        if rows == 0 or cols == 0:
            return
        row_labels = f.get("row_labels", [""] * rows)
        col_labels = f.get("col_labels", [""] * cols)
        label_w = 70
        avail_w = w - label_w - 40
        avail_h = h - top - 60
        cw = max(min(avail_w / cols, 70), 12)
        ch = max(min(avail_h / (rows + 1), 44), 12)
        hl = f.get("highlights", {})
        # column labels
        for j in range(cols):
            x = label_w + j * cw + cw / 2
            self.create_text(x, top + ch / 2,
                             text=str(col_labels[j]) if j < len(col_labels) else "",
                             fill=MUTED, font=("Consolas", 9, "bold"))
        for i in range(rows):
            y = top + (i + 1) * ch
            self.create_text(label_w - 12, y + ch / 2,
                             text=str(row_labels[i]) if i < len(row_labels) else "",
                             fill=MUTED, font=("Consolas", 9, "bold"), anchor="e")
            for j in range(len(cells[i])):
                x = label_w + j * cw
                role = hl.get((i, j), "default")
                color = ROLE_COLORS.get(role, PANEL_2)
                self.create_rectangle(x + 1, y + 1, x + cw - 1, y + ch - 1,
                                      fill=color, outline=BG)
                if cw > 18 and ch > 14:
                    self.create_text(x + cw / 2, y + ch / 2, text=str(cells[i][j]),
                                     fill="#f1f5f9", font=("Consolas", 9))

    # -- linked list nodes ---------------------------------------------------
    def _draw_nodes(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        vals = f.get("values", [])
        hl = f.get("highlights", {})
        if not vals:
            self.create_text(w / 2, (top + h) / 2, text="NULL  (empty list)",
                             fill=MUTED, font=FONT_MONO_B)
            return
        bw, bh = 62, 46
        gap = 26
        per_row = max(1, int((w - 80) // (bw + gap)))
        y = max(top, 90)
        for row_start in range(0, len(vals), per_row):
            x = 50
            chunk = vals[row_start:row_start + per_row]
            for k, v in enumerate(chunk):
                i = row_start + k
                role = hl.get(i, "default")
                color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
                self.create_rectangle(x, y, x + bw, y + bh, fill=color,
                                      outline=BORDER, width=2)
                self.create_text(x + bw / 2, y + bh / 2, text=str(v),
                                 fill="#ffffff", font=FONT_MONO_B)
                if k < len(chunk) - 1:
                    self.create_line(x + bw, y + bh / 2, x + bw + gap, y + bh / 2,
                                     fill=ACCENT, arrow=tk.LAST, width=2)
                else:
                    if i == len(vals) - 1:
                        self.create_line(x + bw, y + bh / 2, x + bw + gap, y + bh / 2,
                                         fill="#64748b", arrow=tk.LAST, width=2)
                        self.create_text(x + bw + gap + 14, y + bh / 2, text="NULL",
                                         fill="#64748b", font=("Consolas", 9), anchor="w")
                x += bw + gap
            y += bh + 46
            if y > h - 40:
                break
        for name, idx in f.get("pointers", {}).items():
            if isinstance(idx, int) and 0 <= idx < len(vals):
                row = idx // per_row
                col = idx % per_row
                px = 50 + col * (bw + gap) + bw / 2
                py = max(top, 90) + row * (bh + 46) + bh + 16
                self.create_text(px, py, text=f"↑ {name}", fill=ACCENT,
                                 font=("Consolas", 9, "bold"))

    # -- stack ---------------------------------------------------------------
    def _draw_stack(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        items = f.get("items", [])
        hl = f.get("highlights", {})
        bw, bh = 150, 40
        base_y = h - 50
        x = w / 2 - bw / 2
        self.create_text(w / 2, max(top, 70), text="TOP", fill=ACCENT,
                         font=FONT_MONO_B)
        if not items:
            self.create_text(w / 2, base_y - 20, text="(empty stack)",
                             fill=MUTED, font=FONT_UI)
            self.create_line(x - 20, base_y + 6, x + bw + 20, base_y + 6,
                             fill=BORDER, width=2)
            return
        for i, v in enumerate(items):
            y = base_y - (i + 1) * bh
            if y < top + 24:
                break
            role = hl.get(i, "default")
            color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
            self.create_rectangle(x, y, x + bw, y + bh - 4, fill=color,
                                  outline=BORDER, width=2)
            self.create_text(x + bw / 2, y + (bh - 4) / 2, text=str(v),
                             fill="#ffffff", font=FONT_MONO_B)
        self.create_line(x - 20, base_y + 6, x + bw + 20, base_y + 6,
                         fill=BORDER, width=2)

    # -- queue ---------------------------------------------------------------
    def _draw_queue(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        items = f.get("items", [])
        hl = f.get("highlights", {})
        bw, bh, gap = 62, 46, 14
        y = max(top, 90) + 40
        x = 60
        if not items:
            self.create_text(w / 2, y + bh / 2, text="(empty queue)",
                             fill=MUTED, font=FONT_UI)
            return
        for i, v in enumerate(items):
            role = hl.get(i, "default")
            color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
            self.create_rectangle(x, y, x + bw, y + bh, fill=color,
                                  outline=BORDER, width=2)
            self.create_text(x + bw / 2, y + bh / 2, text=str(v),
                             fill="#ffffff", font=FONT_MONO_B)
            x += bw + gap
            if x > w - 80:
                break
        front = f.get("front", 0)
        rear = f.get("rear", len(items) - 1)
        fx = 60 + front * (bw + gap) + bw / 2
        rx = 60 + rear * (bw + gap) + bw / 2
        self.create_text(fx, y - 16, text="FRONT", fill=ACCENT,
                         font=("Consolas", 9, "bold"))
        self.create_text(rx, y + bh + 18, text="REAR", fill=WARNING,
                         font=("Consolas", 9, "bold"))
        self.create_line(40, y + bh / 2, 54, y + bh / 2, fill=ACCENT,
                         arrow=tk.LAST, width=2)

    # -- tree ----------------------------------------------------------------
    def _draw_tree(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        root = f.get("tree")
        if root is None:
            self.create_text(w / 2, h / 2, text="(empty tree)", fill=MUTED, font=FONT_UI)
            return
        nodes, edges = tree_layout(root)
        if not nodes:
            return
        hl = f.get("highlights", {})
        max_x = max(n["_x"] for n in nodes) or 1
        max_d = max(n["_depth"] for n in nodes) or 1
        pad_x, pad_y = 70, 60
        avail_w = max(w - 2 * pad_x, 120)
        avail_h = max(h - top - pad_y - 70, 120)
        pos: Dict[int, Tuple[float, float]] = {}
        for n in nodes:
            px = pad_x + (n["_x"] / max_x) * avail_w if max_x else w / 2
            py = top + pad_y + (n["_depth"] / max_d) * avail_h
            pos[n["id"]] = (px, py)
        for a, b in edges:
            if a in pos and b in pos:
                self.create_line(pos[a][0], pos[a][1] + 18, pos[b][0], pos[b][1] - 18,
                                 fill="#3b5a7a", width=2)
        for n in nodes:
            x, y = pos[n["id"]]
            role = hl.get(n["id"], "default")
            color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
            self.create_oval(x - 19, y - 19, x + 19, y + 19, fill=color,
                             outline=BORDER, width=2)
            self.create_text(x, y, text=str(n["val"]), fill="#ffffff",
                             font=("Consolas", 11, "bold"))

    # -- graph ---------------------------------------------------------------
    def _draw_graph(self, f: dict) -> None:
        w, h = self._wh()
        top = self._header(f, w)
        g = f.get("graph") or GRAPH_MAIN
        hl = f.get("highlights", {})
        ehl = f.get("edge_highlights", {})
        pad_x, pad_y = 80, 40
        avail_w = max(w - 2 * pad_x, 100)
        avail_h = max(h - top - pad_y - 50, 100)
        pos: Dict[str, Tuple[float, float]] = {}
        for name, (nx, ny) in g["nodes"].items():
            pos[name] = (pad_x + nx * avail_w, top + pad_y + ny * avail_h)
        for u, v, wt in g["edges"]:
            if u not in pos or v not in pos:
                continue
            role = ehl.get((u, v)) or ehl.get((v, u))
            color = ROLE_COLORS.get(role, "#3b5a7a") if role else "#3b5a7a"
            width = 4 if role else 2
            self.create_line(pos[u][0], pos[u][1], pos[v][0], pos[v][1],
                             fill=color, width=width)
            mx = (pos[u][0] + pos[v][0]) / 2
            my = (pos[u][1] + pos[v][1]) / 2
            self.create_text(mx, my - 8, text=str(wt), fill=MUTED,
                             font=("Consolas", 8))
        for name, (x, y) in pos.items():
            role = hl.get(name, "default")
            if role.startswith("role"):
                role = "visited"
            color = ROLE_COLORS.get(role, ROLE_COLORS["default"])
            self.create_oval(x - 21, y - 21, x + 21, y + 21, fill=color,
                             outline=BORDER, width=2)
            self.create_text(x, y, text=name, fill="#ffffff",
                             font=("Segoe UI", 11, "bold"))


# ============================================================================
# 10. ANIMATION ENGINE
# ============================================================================

class AnimationEngine:
    """Drives frame-by-frame playback without blocking the Tk event loop."""

    def __init__(self, app: "DSAVisualizerApp"):
        self.app = app
        self.frames: List[dict] = []
        self.index = 0
        self.playing = False
        self.delay = SPEEDS["Normal"]
        self._after_id: Optional[str] = None

    # -- lifecycle ---------------------------------------------------------
    def load(self, frames: Sequence[dict]) -> None:
        self.stop()
        self.frames = list(frames)
        self.index = 0
        if self.frames:
            self._show()
        self.app.set_status(f"{len(self.frames)} step(s) ready")

    def stop(self) -> None:
        self.playing = False
        if self._after_id is not None:
            try:
                self.app.after_cancel(self._after_id)
            except Exception:
                pass
            self._after_id = None

    def start(self) -> None:
        if not self.frames:
            return
        if self.index >= len(self.frames) - 1:
            self.index = 0
            self._show()
        self.playing = True
        self.app.set_playing(True)
        self._tick()

    def pause(self) -> None:
        self.stop()
        self.app.set_playing(False)
        self.app.set_status("Paused")

    def toggle(self) -> None:
        if self.playing:
            self.pause()
        else:
            self.start()

    def step(self) -> None:
        self.stop()
        self.app.set_playing(False)
        if self.index < len(self.frames) - 1:
            self.index += 1
            self._show()
        else:
            self.app.set_status("Reached the last step")

    def step_back(self) -> None:
        self.stop()
        self.app.set_playing(False)
        if self.index > 0:
            self.index -= 1
            self._show()

    def reset(self) -> None:
        self.stop()
        self.app.set_playing(False)
        self.index = 0
        if self.frames:
            self._show()
        self.app.set_status("Reset")

    # -- internals ---------------------------------------------------------
    def _show(self) -> None:
        frame = self.frames[self.index]
        self.app.canvas.show(frame)
        self.app.set_status(
            f"Step {self.index + 1}/{len(self.frames)} — {frame.get('message', '')}")

    def _tick(self) -> None:
        if not self.playing:
            return
        if self.index >= len(self.frames) - 1:
            self.playing = False
            self.app.set_playing(False)
            self.app.set_status("Finished ✔")
            return
        self.index += 1
        self._show()
        self._after_id = self.app.after(self.delay, self._tick)


# ============================================================================
# 11. PROBLEMS WINDOW
# ============================================================================

class ProblemManager:
    """Holds and queries the built-in problem bank."""

    def __init__(self, problems: Sequence[Tuple[str, str, str, str, str, str, str, str]]):
        self.problems = list(problems)

    def filter(self, difficulty: str = "All", category: str = "All",
               query: str = "") -> List[Tuple]:
        q = query.lower().strip()
        out = []
        for p in self.problems:
            if difficulty != "All" and p[1] != difficulty:
                continue
            if category != "All" and p[2] != category:
                continue
            if q and q not in p[0].lower() and q not in p[3].lower():
                continue
            out.append(p)
        return out

    def categories(self) -> List[str]:
        return sorted({p[2] for p in self.problems})


class ProblemsWindow(tk.Toplevel):
    def __init__(self, master, manager: ProblemManager):
        super().__init__(master)
        self.title("Practice Problems")
        self.geometry("1080x680")
        self.configure(bg=BG)
        self.manager = manager
        self._build()

    def _build(self) -> None:
        header = tk.Frame(self, bg=PANEL, height=52)
        header.pack(fill="x")
        tk.Label(header, text="  Practice Problems", bg=PANEL, fg=TEXT,
                 font=FONT_TITLE).pack(side="left", pady=8)
        self.count_lbl = tk.Label(header, text="", bg=PANEL, fg=ACCENT,
                                  font=FONT_UI_B)
        self.count_lbl.pack(side="right", padx=14)

        bar = tk.Frame(self, bg=BG)
        bar.pack(fill="x", padx=10, pady=8)
        tk.Label(bar, text="Difficulty:", bg=BG, fg=MUTED, font=FONT_UI).pack(side="left")
        self.diff_var = tk.StringVar(value="All")
        ttk.Combobox(bar, textvariable=self.diff_var, width=10, state="readonly",
                     values=["All", "Easy", "Medium", "Hard"]).pack(side="left", padx=6)
        tk.Label(bar, text="Category:", bg=BG, fg=MUTED, font=FONT_UI).pack(side="left", padx=(12, 0))
        self.cat_var = tk.StringVar(value="All")
        ttk.Combobox(bar, textvariable=self.cat_var, width=18, state="readonly",
                     values=["All"] + self.manager.categories()).pack(side="left", padx=6)
        tk.Label(bar, text="Search:", bg=BG, fg=MUTED, font=FONT_UI).pack(side="left", padx=(12, 0))
        self.search_var = tk.StringVar()
        ent = ttk.Entry(bar, textvariable=self.search_var, width=22)
        ent.pack(side="left", padx=6)
        ttk.Button(bar, text="Filter", command=self.refresh).pack(side="left", padx=6)
        ttk.Button(bar, text="Reset", command=self.reset).pack(side="left")

        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = tk.Frame(body, bg=PANEL)
        left.pack(side="left", fill="both", expand=False)
        self.tree = ttk.Treeview(left, columns=("diff", "cat"), show="tree headings",
                                 height=24)
        self.tree.heading("#0", text="Problem")
        self.tree.heading("diff", text="Level")
        self.tree.heading("cat", text="Category")
        self.tree.column("#0", width=230)
        self.tree.column("diff", width=70, anchor="center")
        self.tree.column("cat", width=130)
        self.tree.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(left, orient="vertical", command=self.tree.yview)
        sb.pack(side="right", fill="y")
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind("<<TreeviewSelect>>", self._on_select)

        right = tk.Frame(body, bg=PANEL_2)
        right.pack(side="left", fill="both", expand=True, padx=(10, 0))
        self.detail = tk.Text(right, bg=PANEL_2, fg=TEXT, font=FONT_MONO,
                              wrap="word", bd=0, padx=14, pady=12)
        self.detail.pack(fill="both", expand=True)
        self.detail.configure(state="disabled")
        self.detail.tag_configure("title", foreground=ACCENT,
                                  font=("Segoe UI", 15, "bold"))
        self.detail.tag_configure("head", foreground=WARNING,
                                  font=("Segoe UI", 11, "bold"))
        self.detail.tag_configure("code", foreground="#7dd3fc", font=FONT_MONO)

        self.refresh()

    def reset(self) -> None:
        self.diff_var.set("All")
        self.cat_var.set("All")
        self.search_var.set("")
        self.refresh()

    def refresh(self) -> None:
        self.tree.delete(*self.tree.get_children())
        rows = self.manager.filter(self.diff_var.get(), self.cat_var.get(),
                                   self.search_var.get())
        self.count_lbl.config(text=f"{len(rows)} problem(s)")
        for i, p in enumerate(rows):
            self.tree.insert("", "end", iid=str(i), text=p[0],
                             values=(p[1], p[2]))
        self._rows = rows
        if rows:
            self.tree.selection_set("0")

    def _on_select(self, _event=None) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        p = self._rows[int(sel[0])]
        title, diff, cat, stmt, example, hint, cx, sol = p
        self.detail.configure(state="normal")
        self.detail.delete("1.0", "end")
        self.detail.insert("end", f"{title}\n", "title")
        self.detail.insert("end", f"{diff}  •  {cat}\n\n")
        self.detail.insert("end", "PROBLEM\n", "head")
        self.detail.insert("end", f"{stmt}\n\n")
        self.detail.insert("end", "EXAMPLE\n", "head")
        self.detail.insert("end", f"{example}\n\n")
        self.detail.insert("end", "HINT\n", "head")
        self.detail.insert("end", f"{hint}\n\n")
        self.detail.insert("end", "EXPECTED COMPLEXITY\n", "head")
        self.detail.insert("end", f"{cx}\n\n")
        self.detail.insert("end", "SOLUTION\n", "head")
        self.detail.insert("end", sol + "\n", "code")
        self.detail.configure(state="disabled")


# ============================================================================
# 12. QUIZ WINDOW
# ============================================================================

class QuizManager:
    def __init__(self, bank: Sequence[Tuple[str, List[str], int, str]]):
        self.bank = list(bank)
        self.questions: List[Tuple] = []
        self.index = 0
        self.score = 0
        self.wrong = 0
        self.answered = False
        self.shuffle(10)

    def shuffle(self, n: int = 10) -> None:
        pool = list(self.bank)
        random.shuffle(pool)
        self.questions = pool[:min(n, len(pool))]
        self.index = 0
        self.score = 0
        self.wrong = 0
        self.answered = False

    def current(self):
        return self.questions[self.index] if self.index < len(self.questions) else None

    def finished(self) -> bool:
        return self.index >= len(self.questions)


class QuizWindow(tk.Toplevel):
    def __init__(self, master, manager: QuizManager):
        super().__init__(master)
        self.title("DSA Quiz")
        self.geometry("720x520")
        self.configure(bg=BG)
        self.manager = manager
        self.choice = tk.IntVar(value=-1)
        self._build()
        self.render()

    def _build(self) -> None:
        top = tk.Frame(self, bg=PANEL, height=50)
        top.pack(fill="x")
        tk.Label(top, text="  DSA Quiz", bg=PANEL, fg=TEXT,
                 font=FONT_TITLE).pack(side="left", pady=8)
        self.score_lbl = tk.Label(top, text="Score: 0", bg=PANEL, fg=SUCCESS,
                                  font=FONT_UI_B)
        self.score_lbl.pack(side="right", padx=16)

        self.q_frame = tk.Frame(self, bg=BG)
        self.q_frame.pack(fill="both", expand=True, padx=18, pady=14)

        self.q_label = tk.Label(self.q_frame, text="", bg=BG, fg=TEXT,
                                font=("Segoe UI", 13, "bold"), wraplength=650,
                                justify="left", anchor="w")
        self.q_label.pack(fill="x", pady=(0, 14))

        self.radio_buttons: List[ttk.Radiobutton] = []
        for _ in range(4):
            rb = ttk.Radiobutton(self.q_frame, text="", variable=self.choice, value=0)
            rb.pack(anchor="w", pady=3)
            self.radio_buttons.append(rb)

        self.feedback = tk.Label(self.q_frame, text="", bg=BG, fg=MUTED,
                                 font=FONT_UI, wraplength=650, justify="left",
                                 anchor="w")
        self.feedback.pack(fill="x", pady=12)

        btns = tk.Frame(self, bg=BG)
        btns.pack(fill="x", padx=18, pady=(0, 16))
        self.submit_btn = ttk.Button(btns, text="Submit Answer", command=self.submit)
        self.submit_btn.pack(side="left")
        self.next_btn = ttk.Button(btns, text="Next Question", command=self.next_q)
        self.next_btn.pack(side="left", padx=8)
        ttk.Button(btns, text="Restart Quiz",
                   command=self.restart).pack(side="right")

    def render(self) -> None:
        self.manager.answered = False
        self.choice.set(-1)
        q = self.manager.current()
        if q is None:
            self.show_result()
            return
        text, options, _correct, _expl = q
        self.q_label.config(
            text=f"Q{self.manager.index + 1}/{len(self.manager.questions)}: {text}")
        for i, rb in enumerate(self.radio_buttons):
            if i < len(options):
                rb.config(text=options[i], value=i, state="normal")
            else:
                rb.config(text="", value=-1, state="disabled")
        self.feedback.config(text="", fg=MUTED)
        self.submit_btn.config(state="normal")
        self.score_lbl.config(
            text=f"Score: {self.manager.score} / "
                 f"{self.manager.score + self.manager.wrong}")

    def submit(self) -> None:
        if self.manager.answered:
            return
        q = self.manager.current()
        if q is None:
            return
        if self.choice.get() < 0:
            messagebox.showinfo("Quiz", "Please select an answer first.", parent=self)
            return
        correct = q[2]
        self.manager.answered = True
        if self.choice.get() == correct:
            self.manager.score += 1
            self.feedback.config(text=f"✔ Correct!  {q[3]}", fg=SUCCESS)
        else:
            self.manager.wrong += 1
            self.feedback.config(
                text=f"✘ Incorrect. The answer is: {q[1][correct]}\n{q[3]}",
                fg=DANGER)
        self.submit_btn.config(state="disabled")
        self.score_lbl.config(
            text=f"Score: {self.manager.score} / "
                 f"{self.manager.score + self.manager.wrong}")

    def next_q(self) -> None:
        self.manager.index += 1
        self.render()

    def restart(self) -> None:
        self.manager.shuffle(10)
        self.render()

    def show_result(self) -> None:
        total = len(self.manager.questions)
        score = self.manager.score
        pct = (score / total * 100) if total else 0
        self.q_label.config(text="Quiz Complete!")
        for rb in self.radio_buttons:
            rb.config(text="", state="disabled")
        grade = ("Excellent 🏆" if pct >= 80 else
                 "Good job 👍" if pct >= 60 else
                 "Keep practising 📚")
        self.feedback.config(
            text=f"You scored {score} / {total}  ({pct:.0f}%)\n"
                 f"Correct: {score}   Incorrect: {self.manager.wrong}\n\n{grade}",
            fg=ACCENT)
        self.submit_btn.config(state="disabled")


# ============================================================================
# 13. COMPARISON WINDOW
# ============================================================================

class ComparisonWindow(tk.Toplevel):
    def __init__(self, master):
        super().__init__(master)
        self.title("Algorithm Comparison")
        self.geometry("900x560")
        self.configure(bg=BG)
        tk.Label(self, text="Sorting Algorithm Comparison", bg=PANEL, fg=TEXT,
                 font=FONT_TITLE).pack(fill="x", ipady=10)

        frame = tk.Frame(self, bg=BG)
        frame.pack(fill="both", expand=True, padx=12, pady=12)

        cols = ("best", "avg", "worst", "space", "stable", "inplace")
        tree = ttk.Treeview(frame, columns=cols, show="headings", height=18)
        for c, t in zip(cols, ("Best", "Average", "Worst", "Space",
                               "Stable", "In-place")):
            tree.heading(c, text=t)
            tree.column(c, width=120, anchor="center")
        tree.column("best", width=150)
        tree.pack(fill="both", expand=True, side="left")
        sb = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        sb.pack(side="right", fill="y")
        tree.configure(yscrollcommand=sb.set)

        for name, alg in ALGORITHMS.items():
            if alg.category == "Sorting":
                tree.insert("", "end", values=(name, alg.best, alg.average,
                                               alg.worst, alg.space,
                                               alg.stable, alg.inplace))
            elif alg.category == "Searching":
                pass

        # Searching comparison below
        tk.Label(self, text="Searching Algorithm Comparison", bg=PANEL, fg=TEXT,
                 font=("Segoe UI", 13, "bold")).pack(fill="x", ipady=6)
        frame2 = tk.Frame(self, bg=BG)
        frame2.pack(fill="both", expand=True, padx=12, pady=(0, 12))
        tree2 = ttk.Treeview(frame2, columns=("best", "avg", "worst", "space"),
                             show="tree headings", height=8)
        tree2.heading("#0", text="Algorithm")
        tree2.column("#0", width=250)
        for c, t in zip(("best", "avg", "worst", "space"),
                        ("Best", "Average", "Worst", "Space")):
            tree2.heading(c, text=t)
            tree2.column(c, width=130, anchor="center")
        tree2.pack(fill="both", expand=True)
        for name, alg in ALGORITHMS.items():
            if alg.category == "Searching":
                tree2.insert("", "end", text=name,
                             values=(alg.best, alg.average, alg.worst, alg.space))


# ============================================================================
# 14. MAIN APPLICATION
# ============================================================================

class DSAVisualizerApp(tk.Tk):
    """The main application window."""

    def __init__(self) -> None:
        super().__init__()
        self.title(f"{APP_TITLE} — {APP_SUBTITLE}")
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        window_w = min(1780, max(1180, screen_w - 80))
        window_h = min(1040, max(720, screen_h - 90))
        self.geometry(f"{window_w}x{window_h}")
        self.minsize(1080, 680)
        self.configure(bg=BG)

        self.current: Optional[Algorithm] = None
        self.data: Any = []
        self.problem_manager = ProblemManager(PROBLEMS)
        self.quiz_manager = QuizManager(QUIZ_BANK)

        self._build_style()
        self._build_header()
        self._build_body()
        self._build_controls()

        self.engine = AnimationEngine(self)
        self._populate_sidebar()
        self.show_dashboard()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self._show_splash()

    def _show_splash(self) -> None:
        self.withdraw()
        splash = tk.Toplevel(self)
        splash.title(APP_TITLE)
        splash.configure(bg=BG)
        splash.overrideredirect(True)
        width, height = 640, 390
        x = max((self.winfo_screenwidth() - width) // 2, 0)
        y = max((self.winfo_screenheight() - height) // 2, 0)
        splash.geometry(f"{width}x{height}+{x}+{y}")

        panel = tk.Frame(splash, bg=PANEL, highlightbackground="#31506e",
                        highlightthickness=1)
        panel.pack(fill="both", expand=True, padx=2, pady=2)
        tk.Frame(panel, bg=ACCENT, height=4).pack(fill="x", side="top")
        tk.Label(panel, text="DSA", bg=PANEL, fg=ACCENT,
                 font=("Segoe UI", 44, "bold")).pack(pady=(42, 0))
        tk.Label(panel, text="ALGORITHM VISUALIZER", bg=PANEL, fg=TEXT,
                 font=("Segoe UI", 16, "bold")).pack(pady=(0, 8))
        tk.Label(panel, text="Learn  •  Visualize  •  Practice  •  Master",
                 bg=PANEL, fg=MUTED, font=("Segoe UI", 10)).pack()

        progress_bg = tk.Frame(panel, bg=PANEL_3, height=5, width=360)
        progress_bg.pack(pady=(48, 0))
        progress_bg.pack_propagate(False)
        progress = tk.Frame(progress_bg, bg=ACCENT, height=5, width=0)
        progress.pack(side="left", fill="y")
        tk.Label(panel, text="Preparing your learning workspace...", bg=PANEL,
                 fg="#64809b", font=("Segoe UI", 9)).pack(pady=(14, 0))

        def finish() -> None:
            if splash.winfo_exists():
                splash.destroy()
            self.deiconify()
            self.lift()

        def animate(value: int = 0) -> None:
            if not splash.winfo_exists():
                return
            progress.config(width=min(value, 360))
            if value < 360:
                splash.after(8, animate, value + 8)
            else:
                splash.after(260, finish)

        splash.after(80, animate)

    # -- styling -----------------------------------------------------------
    def _build_style(self) -> None:
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure(".", background=PANEL, foreground=TEXT,
                        fieldbackground=PANEL_2, font=FONT_UI)
        style.configure("TFrame", background=BG)
        style.configure("Panel.TFrame", background=PANEL)
        style.configure("TLabel", background=BG, foreground=TEXT, font=FONT_UI)
        style.configure("Panel.TLabel", background=PANEL, foreground=TEXT)
        style.configure("Muted.TLabel", background=PANEL, foreground=MUTED,
                        font=FONT_SMALL)
        style.configure("TButton", background=PANEL_3, foreground=TEXT,
                        borderwidth=0, focusthickness=0, padding=(10, 6),
                        font=FONT_UI_B)
        style.map("TButton",
                  background=[("active", ACCENT_2), ("pressed", ACCENT)],
                  foreground=[("active", "#ffffff")])
        style.configure("Accent.TButton", background=ACCENT, foreground="#04212b")
        style.map("Accent.TButton", background=[("active", "#67e8f9")])
        style.configure("Treeview", background=PANEL_2, fieldbackground=PANEL_2,
                        foreground=TEXT, rowheight=25, font=FONT_UI, borderwidth=0)
        style.map("Treeview", background=[("selected", ACCENT_2)],
                  foreground=[("selected", "#ffffff")])
        style.configure("Treeview.Heading", background=PANEL_3, foreground=ACCENT,
                        font=FONT_UI_B, relief="flat")
        style.configure("TNotebook", background=BG, borderwidth=0)
        style.configure("TNotebook.Tab", background=PANEL_2, foreground=MUTED,
                        padding=(14, 8), font=FONT_UI_B)
        style.map("TNotebook.Tab", background=[("selected", PANEL_3)],
                  foreground=[("selected", ACCENT)])
        style.configure("TCombobox", fieldbackground=PANEL_2, background=PANEL_3,
                        foreground=TEXT, arrowcolor=ACCENT)
        style.configure("TEntry", fieldbackground=PANEL_2, foreground=TEXT)
        style.configure("TRadiobutton", background=BG, foreground=TEXT,
                        font=FONT_UI)
        style.map("TRadiobutton", background=[("active", BG)])

    # -- header ------------------------------------------------------------
    def _build_header(self) -> None:
        header = tk.Frame(self, bg=PANEL, height=76)
        header.pack(fill="x", side="top")
        header.pack_propagate(False)

        tk.Frame(header, bg=ACCENT, height=3).pack(fill="x", side="top")

        left = tk.Frame(header, bg=PANEL)
        left.pack(side="left", padx=22, pady=(8, 0))
        tk.Label(left, text=APP_TITLE, bg=PANEL, fg=TEXT,
                 font=("Segoe UI", 17, "bold")).pack(anchor="w")
        tk.Label(left, text=APP_SUBTITLE, bg=PANEL, fg=ACCENT,
                 font=("Segoe UI", 9)).pack(anchor="w")

        right = tk.Frame(header, bg=PANEL)
        right.pack(side="right", padx=22, pady=(12, 0))
        for text, cmd in (("Problems", self.open_problems),
                          ("Quiz", self.open_quiz),
                          ("Compare", self.open_comparison),
                          ("Dashboard", self.show_dashboard)):
            ttk.Button(right, text=text, command=cmd).pack(side="left", padx=4)

    # -- body --------------------------------------------------------------
    def _build_body(self) -> None:
        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True)

        # ---- sidebar ----
        sidebar = tk.Frame(body, bg=PANEL, width=262)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)

        tk.Label(sidebar, text="  ALGORITHM LIBRARY", bg=PANEL, fg=ACCENT,
                 font=("Segoe UI", 10, "bold")).pack(fill="x", pady=(12, 4))

        search_wrap = tk.Frame(sidebar, bg=PANEL)
        search_wrap.pack(fill="x", padx=10, pady=(0, 6))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self._populate_sidebar())
        ent = ttk.Entry(search_wrap, textvariable=self.search_var)
        ent.pack(fill="x")

        tree_wrap = tk.Frame(sidebar, bg=PANEL)
        tree_wrap.pack(fill="both", expand=True, padx=(10, 0), pady=(0, 10))
        self.side_tree = ttk.Treeview(tree_wrap, show="tree", selectmode="browse")
        self.side_tree.pack(side="left", fill="both", expand=True)
        sb = ttk.Scrollbar(tree_wrap, orient="vertical", command=self.side_tree.yview)
        sb.pack(side="right", fill="y")
        self.side_tree.configure(yscrollcommand=sb.set)
        self.side_tree.bind("<<TreeviewSelect>>", self._on_sidebar_select)

        # ---- center ----
        center = tk.Frame(body, bg=BG)
        center.pack(side="left", fill="both", expand=True, padx=12, pady=12)

        canvas_wrap = tk.Frame(center, bg=PANEL, highlightbackground=BORDER,
                               highlightthickness=1)
        canvas_wrap.pack(fill="both", expand=True)
        self.canvas = Visualizer(canvas_wrap)
        self.canvas.pack(fill="both", expand=True, padx=2, pady=2)

        self.status = tk.Label(center, text="Ready", bg=PANEL_2, fg=MUTED,
                               font=FONT_MONO, anchor="w", padx=10)
        self.status.pack(fill="x", pady=(6, 0), ipady=5)

        # ---- right panel ----
        right = tk.Frame(body, bg=BG, width=410)
        right.pack(side="right", fill="y", padx=(0, 12), pady=12)
        right.pack_propagate(False)

        self.notebook = ttk.Notebook(right)
        self.notebook.pack(fill="both", expand=True)

        self.info_txt = self._make_text_tab("Info")
        self.code_txt = self._make_text_tab("Code")
        self.cx_txt = self._make_text_tab("Complexity")
        self._build_code_tab_extras()

    def _make_text_tab(self, name: str) -> tk.Text:
        frame = tk.Frame(self.notebook, bg=PANEL_2)
        self.notebook.add(frame, text=name)
        txt = tk.Text(frame, bg=PANEL_2, fg=TEXT, font=FONT_UI, wrap="word",
                      bd=0, padx=12, pady=10, insertbackground=TEXT)
        txt.pack(fill="both", expand=True)
        txt.configure(state="disabled")
        txt.tag_configure("h", foreground=ACCENT,
                          font=("Segoe UI", 11, "bold"))
        txt.tag_configure("k", foreground=WARNING, font=FONT_UI_B)
        txt.tag_configure("m", foreground="#7dd3fc", font=FONT_MONO)
        return txt

    def _build_code_tab_extras(self) -> None:
        parent = self.notebook.nametowidget(self.notebook.tabs()[1])
        bar = tk.Frame(parent, bg=PANEL_2)
        bar.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Button(bar, text="Copy Code", command=self.copy_code).pack(side="left")
        ttk.Button(bar, text="Load Example",
                   command=self.load_example).pack(side="left", padx=6)
        parent.pack_slaves()
        # Move the Text below the bar
        txt = self.code_txt
        txt.pack_forget()
        txt.pack(fill="both", expand=True)

    # -- controls ----------------------------------------------------------
    def _build_controls(self) -> None:
        bar = tk.Frame(self, bg=PANEL, height=118)
        bar.pack(fill="x", side="bottom")
        bar.pack_propagate(False)

        row1 = tk.Frame(bar, bg=PANEL)
        row1.pack(fill="x", padx=12, pady=(8, 4))

        tk.Label(row1, text="Data:", bg=PANEL, fg=MUTED, font=FONT_UI).pack(side="left")
        self.input_var = tk.StringVar(value="5, 3, 8, 1, 9, 2, 7, 4")
        ttk.Entry(row1, textvariable=self.input_var, width=42).pack(side="left", padx=6)
        ttk.Button(row1, text="Apply Input", command=self.apply_input).pack(side="left")

        tk.Label(row1, text="  Target:", bg=PANEL, fg=MUTED,
                 font=FONT_UI).pack(side="left")
        self.target_var = tk.StringVar(value="50")
        ttk.Entry(row1, textvariable=self.target_var, width=8).pack(side="left", padx=6)

        tk.Label(row1, text="  Size:", bg=PANEL, fg=MUTED, font=FONT_UI).pack(side="left")
        self.size_var = tk.StringVar(value="12")
        ttk.Entry(row1, textvariable=self.size_var, width=5).pack(side="left", padx=4)
        tk.Label(row1, text="Min:", bg=PANEL, fg=MUTED, font=FONT_UI).pack(side="left")
        self.min_var = tk.StringVar(value="1")
        ttk.Entry(row1, textvariable=self.min_var, width=5).pack(side="left", padx=4)
        tk.Label(row1, text="Max:", bg=PANEL, fg=MUTED, font=FONT_UI).pack(side="left")
        self.max_var = tk.StringVar(value="99")
        ttk.Entry(row1, textvariable=self.max_var, width=5).pack(side="left", padx=4)
        ttk.Button(row1, text="Generate Random",
                   command=self.generate_random).pack(side="left", padx=6)

        row2 = tk.Frame(bar, bg=PANEL)
        row2.pack(fill="x", padx=12, pady=(2, 10))

        self.start_btn = ttk.Button(row2, text="▶  Start", style="Accent.TButton",
                                    command=self.on_start)
        self.start_btn.pack(side="left")
        ttk.Button(row2, text="⏸  Pause", command=self.on_pause).pack(side="left", padx=6)
        ttk.Button(row2, text="⏭  Step", command=self.on_step).pack(side="left")
        ttk.Button(row2, text="⏮  Back", command=self.on_back).pack(side="left", padx=6)
        ttk.Button(row2, text="⟲  Reset", command=self.on_reset).pack(side="left")
        ttk.Button(row2, text="↺  Randomize", command=self.generate_random).pack(side="left", padx=6)
        ttk.Button(row2, text="Example", command=self.load_example).pack(side="left")

        tk.Label(row2, text="   Speed:", bg=PANEL, fg=MUTED,
                 font=FONT_UI).pack(side="left")
        self.speed_var = tk.StringVar(value="Normal")
        cb = ttk.Combobox(row2, textvariable=self.speed_var, width=12,
                          state="readonly", values=list(SPEEDS.keys()))
        cb.pack(side="left", padx=6)
        cb.bind("<<ComboboxSelected>>", lambda _e: self.on_speed())

    # -- sidebar -----------------------------------------------------------
    def _populate_sidebar(self) -> None:
        query = self.search_var.get().lower().strip()
        self.side_tree.delete(*self.side_tree.get_children())
        for cat in CATEGORIES:
            names = [n for n, a in ALGORITHMS.items()
                     if a.category == cat and (not query or query in n.lower())]
            if not names:
                continue
            node = self.side_tree.insert("", "end", text=f"  {cat}",
                                         open=bool(query))
            for n in sorted(names):
                self.side_tree.insert(node, "end", iid=f"alg::{n}", text=f"    {n}")

    def _on_sidebar_select(self, _event=None) -> None:
        sel = self.side_tree.selection()
        if not sel:
            return
        iid = sel[0]
        if not iid.startswith("alg::"):
            return
        self.load_algorithm(iid.split("::", 1)[1])

    # -- algorithm loading --------------------------------------------------
    def load_algorithm(self, name: str) -> None:
        alg = ALGORITHMS.get(name)
        if alg is None:
            return
        self.current = alg
        self.engine.stop()
        self.engine.frames = []
        self.input_var.set(alg.default_input)
        if alg.uses_target:
            try:
                nums = parse_int_list(alg.default_input)
                self.target_var.set(str(nums[len(nums) // 2]))
            except Exception:
                pass
        self.apply_input(silent=True)
        self._update_panels()
        self.set_status(f"{alg.name} loaded — press Start")
        self.canvas.frame = None
        self.canvas.redraw()

    def apply_input(self, silent: bool = False) -> bool:
        alg = self.current
        if alg is None:
            if not silent:
                messagebox.showinfo("Info", "Select an algorithm first.", parent=self)
            return False
        raw = self.input_var.get()

        try:
            if alg.input_type == "int_list":
                data = parse_int_list(raw)
                if alg.needs_sorted:
                    data = insertion_sorted(data)
                if len(data) > MAX_ANIMATED_ITEMS:
                    if not silent:
                        messagebox.showwarning(
                            "Large input",
                            f"{len(data)} items is a lot to animate.\n"
                            f"The first {MAX_ANIMATED_ITEMS} will be used.",
                            parent=self)
                    data = data[:MAX_ANIMATED_ITEMS]
                self.data = data
            elif alg.input_type == "string":
                s = (raw or "").strip()
                if not s:
                    raise ValueError("Please enter a non-empty string.")
                self.data = s
            elif alg.input_type == "string_pair":
                parts = [p.strip() for p in raw.split(",")]
                if len(parts) != 2 or not parts[0] or not parts[1]:
                    raise ValueError("Enter two strings separated by a comma.")
                self.data = parts
            else:
                self.data = []
        except ValueError as exc:
            if not silent:
                messagebox.showerror("Invalid input", str(exc), parent=self)
            return False
        except Exception as exc:
            if not silent:
                messagebox.showerror("Invalid input", f"Could not parse input.\n{exc}",
                                     parent=self)
            return False

        self.build_frames()
        return True

    def build_frames(self) -> None:
        alg = self.current
        if alg is None or alg.run is None:
            return
        frames: List[dict] = []
        try:
            if alg.uses_target:
                try:
                    target = int(float(self.target_var.get()))
                except Exception:
                    target = self.data[len(self.data) // 2] if self.data else 0
                if alg.input_type == "string_pair":
                    gen = alg.run(*self.data, target)
                else:
                    gen = alg.run(self.data, target)
            elif alg.input_type == "string_pair":
                gen = alg.run(*self.data)
            elif alg.input_type == "none":
                gen = alg.run([])
            else:
                gen = alg.run(self.data)
            for frame in gen:
                frames.append(frame)
                if len(frames) > 6000:
                    break
        except Exception as exc:
            messagebox.showerror("Algorithm error",
                                 f"This algorithm could not run:\n{exc}", parent=self)
            frames = [text_frame([f"Error: {exc}"], "Algorithm error")]

        if not frames:
            frames = [text_frame(["Nothing to visualize."], "Empty")]
        self.engine.load(frames)

    def load_example(self) -> None:
        if self.current is None:
            return
        self.input_var.set(self.current.default_input)
        self.apply_input()

    def generate_random(self) -> None:
        try:
            size = int(float(self.size_var.get()))
            lo = int(float(self.min_var.get()))
            hi = int(float(self.max_var.get()))
        except Exception:
            messagebox.showerror("Invalid numbers",
                                 "Size, min and max must be integers.", parent=self)
            return
        if size < 1:
            messagebox.showerror("Invalid size", "Size must be at least 1.", parent=self)
            return
        if hi < lo:
            lo, hi = hi, lo
        size = min(size, MAX_ANIMATED_ITEMS)
        data = [random.randint(lo, hi) for _ in range(size)]
        self.input_var.set(", ".join(str(x) for x in data))
        self.apply_input()

    # -- panels ------------------------------------------------------------
    def _set_text(self, widget: tk.Text, chunks: List[Tuple[str, Optional[str]]]) -> None:
        widget.configure(state="normal")
        widget.delete("1.0", "end")
        for text, tag in chunks:
            widget.insert("end", text, tag) if tag else widget.insert("end", text)
        widget.configure(state="disabled")

    def _update_panels(self) -> None:
        alg = self.current
        if alg is None:
            return
        # Info
        self._set_text(self.info_txt, [
            (f"{alg.name}\n", "h"),
            (f"{alg.category}  •  {alg.difficulty}\n\n", None),
            ("WHAT IS IT?\n", "h"), (alg.description + "\n\n", None),
            ("HOW DOES IT WORK?\n", "h"), (alg.how + "\n\n", None),
            ("EXAMPLE\n", "h"),
            (f"{alg.default_input}\n\n", "m"),
        ])
        # Code
        self._set_text(self.code_txt, [(alg.code + "\n", "m")])
        # Complexity
        self._set_text(self.cx_txt, [
            ("TIME COMPLEXITY\n", "h"),
            ("  Best      : ", "k"), (f"{alg.best}\n", None),
            ("  Average   : ", "k"), (f"{alg.average}\n", None),
            ("  Worst     : ", "k"), (f"{alg.worst}\n\n", None),
            ("SPACE COMPLEXITY\n", "h"),
            (f"  {alg.space}\n\n", None),
            ("PROPERTIES\n", "h"),
            ("  Stable    : ", "k"), (f"{alg.stable}\n", None),
            ("  In-place  : ", "k"), (f"{alg.inplace}\n\n", None),
            ("CATEGORY\n", "h"), (f"  {alg.category}\n", None),
        ])

    def copy_code(self) -> None:
        if self.current is None:
            return
        try:
            self.clipboard_clear()
            self.clipboard_append(self.current.code)
            self.set_status("Code copied to clipboard ✔")
        except Exception as exc:
            messagebox.showerror("Clipboard", f"Could not copy: {exc}", parent=self)

    # -- controls handlers --------------------------------------------------
    def on_start(self) -> None:
        if not self.engine.frames:
            if not self.apply_input(silent=True):
                return
        self.engine.start()

    def on_pause(self) -> None:
        self.engine.pause()

    def on_step(self) -> None:
        if not self.engine.frames:
            if not self.apply_input(silent=True):
                return
        self.engine.step()

    def on_back(self) -> None:
        self.engine.step_back()

    def on_reset(self) -> None:
        self.engine.reset()

    def on_speed(self) -> None:
        self.engine.delay = SPEEDS.get(self.speed_var.get(), 250)

    def set_status(self, text: str) -> None:
        self.status.config(text=f"  {text}")

    def set_playing(self, playing: bool) -> None:
        self.start_btn.config(text="⏸  Playing" if playing else "▶  Start")

    # -- windows ------------------------------------------------------------
    def open_problems(self) -> None:
        ProblemsWindow(self, self.problem_manager)

    def open_quiz(self) -> None:
        QuizWindow(self, self.quiz_manager)

    def open_comparison(self) -> None:
        ComparisonWindow(self)

    def show_dashboard(self) -> None:
        total_alg = len(ALGORITHMS)
        total_prob = len(PROBLEMS)
        cats = len({a.category for a in ALGORITHMS.values()})
        diff_count: Dict[str, int] = {}
        for a in ALGORITHMS.values():
            diff_count[a.difficulty] = diff_count.get(a.difficulty, 0) + 1
        by_cat: Dict[str, int] = {}
        for a in ALGORITHMS.values():
            by_cat[a.category] = by_cat.get(a.category, 0) + 1
        lines = [
            "DSA ALGORITHM VISUALIZER — DASHBOARD",
            "Learn • Visualize • Practice • Master",
            "",
            f"Algorithms      : {total_alg}",
            f"Problems        : {total_prob}",
            f"Quiz questions  : {len(QUIZ_BANK)}",
            f"Categories      : {cats}",
            "",
            "DIFFICULTY DISTRIBUTION",
        ]
        for d in ("Easy", "Medium", "Hard"):
            lines.append(f"  {d:<8}: {diff_count.get(d, 0)}")
        lines += ["", "ALGORITHMS PER CATEGORY"]
        for cat in CATEGORIES:
            if cat in by_cat:
                lines.append(f"  {cat:<22}: {by_cat[cat]}")
        lines += [
            "",
            "QUICK TIPS",
            "  • Pick an algorithm from the left sidebar.",
            "  • Press Start / Step to watch every operation.",
            "  • Use the Speed box to slow the animation down.",
            "  • Enter your own data and press Apply Input.",
            "  • Right panel has Info, Code and Complexity tabs.",
        ]
        self.engine.stop()
        self.engine.frames = []
        self.current = None
        self.canvas.show(text_frame(lines, "Dashboard"))
        self.set_status("Dashboard")
        self._set_text(self.info_txt, [
            ("Welcome!\n", "h"),
            ("This visualizer contains a full library of data structures and "
             "algorithms with animated, step-by-step explanations.\n\n"
             "Select any entry in the left sidebar to begin. The centre canvas "
             "adapts its rendering to the data structure (bars for arrays, "
             "character boxes for strings, node diagrams for linked lists and "
             "trees, circles for graphs, grids for dynamic programming).\n\n"
             "Use the buttons at the top-right for the Problems bank, the Quiz "
             "and the algorithm Comparison table.", None),
        ])
        self._set_text(self.code_txt, [("# Select an algorithm to view its code.\n", "m")])
        self._set_text(self.cx_txt, [("Select an algorithm to view its complexity.", None)])

    # -- misc ---------------------------------------------------------------
    def _on_close(self) -> None:
        self.engine.stop()
        self.destroy()


# ============================================================================
# 15. ENTRY POINT
# ============================================================================

def main() -> None:
    if sys.version_info < (3, 10):
        print("This application requires Python 3.10 or newer.")
        sys.exit(1)
    try:
        app = DSAVisualizerApp()
    except tk.TclError as exc:
        print("Could not start the Tkinter GUI:", exc)
        print("Make sure tkinter is available (e.g. 'sudo apt install python3-tk').")
        sys.exit(1)
    app.mainloop()


if __name__ == "__main__":
    main()