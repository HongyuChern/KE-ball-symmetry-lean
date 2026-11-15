#!/usr/bin/env python3
"""Run the pinned KE ball Comparator and write evidence for the selected scope."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
LIB = ROOT / "KEBallComparator"
PACKAGES = ROOT / ".lake" / "packages"
PAPER = ROOT / "paper" / "chen-KE-Ball-Symmetry-2026.tex"
PAPER_SHA256 = "1f8dad706f1513883619f2b4d03c48364b26dbdff7f2ca619097222910469d81"


def sha256(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def source_hashes():
    files = [ROOT / name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    files.extend(ROOT.glob("*.lean"))
    files.extend((PAPER, Path(__file__).resolve()))
    for directory in ("KEBall", "KEBallProbe", "Drafts", "KEBallComparator",
                      "verification/audits", "verification/validation"):
        files.extend((ROOT / directory).rglob("*.lean"))
    files.extend(LIB.glob("config*.json"))
    return {str(path.relative_to(ROOT)): sha256(path) for path in sorted(files)}


def source_revision(hashed_paths):
    """Record the project checkout when the source is inside its own Git worktree."""
    root = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", "--show-toplevel"],
        capture_output=True, text=True,
    )
    if root.returncode or Path(root.stdout.strip()).resolve() != ROOT:
        return None

    def git(*args):
        return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()

    head = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", "--verify", "HEAD"],
        capture_output=True, text=True,
    )
    if head.returncode:
        return None
    tracked = set(git("ls-files", "-z").split("\0"))
    return {
        "commit": head.stdout.strip(),
        "tree": git("rev-parse", f"{head.stdout.strip()}^{{tree}}"),
        "tracked_files_clean": not git("status", "--porcelain=v1", "--untracked-files=no"),
        "all_hashed_inputs_tracked": tracked.issuperset(hashed_paths),
    }


def executable(name, override=None):
    found = shutil.which(os.environ.get(override, name) if override else name)
    if found is None:
        raise RuntimeError(f"{name} is required. See KEBallComparator/README.md.")
    return Path(found).resolve()


def dependency_revisions(*, allow_missing=False):
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    revisions = {}
    for package in manifest["packages"]:
        name = package["name"]
        checkout = PACKAGES / name
        if allow_missing and not checkout.exists():
            continue
        revision = subprocess.check_output(
            ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"{name} is at {revision}, expected {package['rev']}")
        changes = subprocess.check_output(
            ["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"],
            text=True,
        )
        if changes:
            raise RuntimeError(f"{name} has modified tracked files")
        revisions[name] = revision
    return revisions


def run_logged(command, log, environment=None):
    print(f"Running {command[0]} ({log})", flush=True)
    with log.open("w") as output:
        result = subprocess.run(
            command, cwd=ROOT, env=environment, stdout=output, stderr=subprocess.STDOUT
        )
    return result.returncode


def comparator_config(release):
    config_path = LIB / ("config.json" if release else "config.preflight.json")
    config = json.loads(config_path.read_text())
    release_config = json.loads((LIB / "config.json").read_text())
    preflight_config = json.loads((LIB / "config.preflight.json").read_text())
    if release_config["enable_nanoda"] is not True or preflight_config["enable_nanoda"] is not False:
        raise RuntimeError("The two checked-in configs have inconsistent kernel settings")
    axioms = ["propext", "Classical.choice", "Quot.sound"]
    for scope in (release_config, preflight_config):
        if (scope["challenge_module"] != "KEBallComparator.Challenge"
                or scope["solution_module"] != "KEBallComparator.Solution"
                or scope["definition_names"] or scope["permitted_axioms"] != axioms):
            raise RuntimeError("The Comparator configuration changed the proof interface or axioms")
    target_names = [
        f"KEBallComparator.Targets.{name}"
        for name in re.findall(r"^theorem (\w+)", (LIB / "Challenge.lean").read_text(), re.MULTILINE)
    ]
    pending = {
        "KEBallComparator.Targets.subcriticalAttainment",
        "KEBallComparator.Targets.criticalInequality",
    }
    if (release_config["theorem_names"] != target_names
            or not pending.issubset(target_names)
            or preflight_config["theorem_names"] != [name for name in target_names if name not in pending]):
        raise RuntimeError("The configured targets differ from the current challenge")

    return config_path, config


def success_messages(release):
    messages = ["Lean default kernel accepts the solution", "Your solution is okay!"]
    if release:
        messages.insert(0, "Nanoda kernel accepts the solution")
    return messages


def verify_receipt(path):
    """Check a saved receipt against the current sources and accompanying logs."""
    receipt = json.loads(path.read_text())
    mode = receipt["mode"]
    if mode not in {"linux-release", "linux-preflight", "macos-development"}:
        raise RuntimeError(f"Unknown verification mode: {mode}")
    release = mode == "linux-release"
    config_path, config = comparator_config(release)
    config_name = str(config_path.relative_to(ROOT))
    if (receipt["config"] != config_name
            or receipt["config_sha256"] != sha256(config_path)
            or receipt["theorems"] != config["theorem_names"]
            or receipt["permitted_axioms"] != config["permitted_axioms"]):
        raise RuntimeError("The receipt does not match the checked-in Comparator configuration")

    if sha256(PAPER) != PAPER_SHA256 or receipt["source_sha256"] != source_hashes():
        raise RuntimeError("The receipt does not match the current verification sources")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {package["name"]: package["rev"] for package in manifest["packages"]}
    if receipt["dependency_revisions"] != pins:
        raise RuntimeError("The receipt does not match the locked dependency revisions")

    for name in ("build", "comparator"):
        if receipt[f"{name}_log_sha256"] != sha256(path.with_name(f"{name}.log")):
            raise RuntimeError(f"The {name} log differs from the receipt")
    lines = set(path.with_name("comparator.log").read_text(errors="replace").splitlines())
    markers = {message: message in lines for message in success_messages(release)}
    if (receipt["success_markers"] != markers or not all(markers.values())
            or receipt["comparator_exit_code"] != 0 or receipt["sources_unchanged"] is not True
            or receipt["accepted"] is not True or receipt["release_verified"] is not release):
        raise RuntimeError("The receipt and logs do not establish success for this verification mode")
    print(f"Receipt matches the sources, configuration, and logs ({mode}, {len(config['theorem_names'])} targets).")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preflight", action="store_true", help="check the already-proven targets")
    parser.add_argument("--output", type=Path, help="write logs to a new directory")
    parser.add_argument("--verify-receipt", type=Path, help="check a saved receipt and its sibling logs")
    args = parser.parse_args()
    if args.verify_receipt:
        if args.preflight or args.output:
            parser.error("--verify-receipt is independent of --preflight and --output")
        verify_receipt(args.verify_receipt.resolve())
        return 0

    operating_system = platform.system()
    release = not args.preflight
    config_path, config = comparator_config(release)
    if sha256(PAPER) != PAPER_SHA256:
        raise RuntimeError("The release manuscript differs from the selected final source")

    if operating_system == "Linux":
        if os.geteuid() == 0:
            raise RuntimeError("Run Comparator from an unprivileged Linux user")
        landrun = executable("landrun", "COMPARATOR_LANDRUN")
        with landrun.open("rb") as binary:
            if binary.read(4) != b"\x7fELF":
                raise RuntimeError("The Linux check requires the compiled Landrun executable")
        systemd_run = executable("systemd-run")
        mode = "linux-release" if release else "linux-preflight"
    elif operating_system == "Darwin" and args.preflight:
        landrun = PACKAGES / "Comparator" / "scripts" / "fake-landrun.sh"
        systemd_run = None
        mode = "macos-development"
        print("Using Comparator's macOS development shim. This is a Lean-kernel preflight.")
    else:
        raise RuntimeError("The dual-kernel release check requires unprivileged Linux with Landrun")

    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("lake is required")
    nanoda = executable("nanoda_bin", "COMPARATOR_NANODA") if release else None
    output = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="ke-comparator."))
    if args.output:
        output.mkdir(parents=True, exist_ok=False)

    dependency_revisions(allow_missing=True)
    before = source_hashes()
    checkout = source_revision(before)
    tools = ["@Comparator/comparator", "@lean4export/lean4export"]
    build_log = output / "build.log"
    if run_logged([lake, "build", *tools], build_log):
        raise RuntimeError(f"Comparator tool build failed. See {build_log}")
    revisions = dependency_revisions()

    comparator = PACKAGES / "Comparator" / ".lake" / "build" / "bin" / "comparator"
    exporter = PACKAGES / "lean4export" / ".lake" / "build" / "bin" / "lean4export"
    environment = os.environ.copy()
    environment["COMPARATOR_LANDRUN"] = str(landrun)
    environment["COMPARATOR_LEAN4EXPORT"] = str(exporter)
    environment["TMPDIR"] = str(output)
    if nanoda:
        environment["COMPARATOR_NANODA"] = str(nanoda)
    environment["PATH"] = os.pathsep.join([str(comparator.parent), str(exporter.parent), environment["PATH"]])

    command = [lake, "env", str(comparator), str(config_path.relative_to(ROOT))]
    if systemd_run:
        pass_env = ["PATH", "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "TMPDIR"]
        if nanoda:
            pass_env.append("COMPARATOR_NANODA")
        command = [
            str(systemd_run), "--user", "--wait", "--pipe", "--collect",
            "--property=RestrictAddressFamilies=~AF_UNIX", f"--working-directory={ROOT}",
            *(f"--setenv={name}={environment[name]}" for name in pass_env), "--", *command,
        ]

    log = output / "comparator.log"
    started_utc = datetime.now(timezone.utc)
    started = time.monotonic()
    exit_code = run_logged(command, log, environment)
    elapsed = time.monotonic() - started
    finished_utc = datetime.now(timezone.utc)
    lines = log.read_text(errors="replace").splitlines()
    messages = success_messages(release)
    source_unchanged = (
        before == source_hashes() and revisions == dependency_revisions()
        and checkout == source_revision(before)
    )
    accepted = exit_code == 0 and source_unchanged and all(message in lines for message in messages)
    binaries = {"comparator": comparator, "lean4export": exporter, "landrun": landrun}
    if nanoda:
        binaries["nanoda"] = nanoda
    receipt = {
        "mode": mode,
        "command": command,
        "working_directory": str(ROOT),
        "platform": platform.platform(),
        "started_utc": started_utc.isoformat(),
        "finished_utc": finished_utc.isoformat(),
        "elapsed_seconds": round(elapsed, 3),
        "lean_version": subprocess.check_output([lake, "env", "lean", "--version"], cwd=ROOT, text=True).strip(),
        "config": str(config_path.relative_to(ROOT)),
        "config_sha256": before[str(config_path.relative_to(ROOT))],
        "theorems": config["theorem_names"],
        "permitted_axioms": config["permitted_axioms"],
        "sources_unchanged": source_unchanged,
        "source_revision": checkout,
        "source_sha256": before,
        "dependency_revisions": revisions,
        "binary_sha256": {name: sha256(path) for name, path in binaries.items()},
        "build_log_sha256": sha256(build_log),
        "comparator_log_sha256": sha256(log),
        "comparator_exit_code": exit_code,
        "success_markers": {message: message in lines for message in messages},
        "accepted": accepted,
        "release_verified": release and accepted,
    }
    evidence = output / "receipt.json"
    evidence.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(f"Evidence: {evidence}")
    for message in messages:
        if message in lines:
            print(message)
    if not accepted:
        print("\n".join(lines[-35:]), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, KeyError, ValueError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
