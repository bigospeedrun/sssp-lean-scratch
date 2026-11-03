"""Stage this repository the way bigospeedrun/verifier builds a directed-sssp submission.

Usage: python3 -I ci/stage_verifier.py VERIFIER_CHECKOUT
The verifier's own code writes lakefile.toml (lakefile, dependency_root_options), its committed
lake-manifest.json and lean-toolchain are copied, the fork is cloned at the profile's pin and its
Frontier modules are copied in (never committed), and VerifierChallenge.lean is the generated target.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path.cwd()
VER = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(VER / 'scripts'))
import submissions  # noqa: E402
import verifier  # noqa: E402

profile = json.loads((VER / 'profiles/direct.json').read_text())['directed-sssp']
deps = profile['solution_dependencies']
roots = profile['source_roots'] + [r for d in deps for r in d['source_roots']] + ['VerifierChallenge', 'VerifierAudit']
for d in deps:
    target = HERE / '.fork'
    subprocess.check_call(['git', 'clone', '--quiet', '--filter=blob:none', d['repo_url'], str(target)])
    subprocess.check_call(['git', '-C', str(target), 'checkout', '--quiet', d['commit']])
    for root in d['source_roots']:
        src = target / d.get('source_subdir', '') / root
        if (HERE / root).exists():
            raise SystemExit(f'{root} already exists here')
        shutil.copytree(src, HERE / root)
        shutil.copyfile(src.with_suffix('.lean'), HERE / f'{root}.lean')
(HERE / 'lakefile.toml').write_text(verifier.lakefile(
    roots, profile['manifest_file'],
    profile.get('auto_implicit', False), verifier.dependency_root_options(deps, profile['source_roots'])))
shutil.copyfile(VER / profile['manifest_file'], HERE / 'lake-manifest.json')
(HERE / 'lean-toolchain').write_text(profile['lean_toolchain'] + '\n')
sub = {'schema_version': 1, 'problem': 'directed-sssp', 'bound': 'n log^3/4 ; n log^11/12',
       'repo_url': 'https://github.com/bigospeedrun/sssp-lean-scratch', 'commit': '0' * 40, 'authors': []}
(HERE / 'VerifierChallenge.lean').write_text(submissions.challenge_source(sub))
# As verifier.prepare writes it: the solution module, then #print axioms of each theorem name.
(HERE / 'VerifierAudit.lean').write_text('import ' + profile['solution_module'] + '\n' +
                                      ''.join('#print axioms ' + n + '\n' for n in profile['theorem_names']))
print((HERE / 'lakefile.toml').read_text())
