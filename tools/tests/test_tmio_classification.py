"""Regression tests for the source preflight, without Lean or repository edits."""

from __future__ import annotations

import importlib.util
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


_TOOL = Path(__file__).resolve().parents[1] / "tmio_classification.py"
_SPEC = importlib.util.spec_from_file_location("tmio_classification", _TOOL)
assert _SPEC is not None and _SPEC.loader is not None
classification = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(classification)


class TMIOClassificationTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "theorem").mkdir()

    def write(self, source: str, path: str = "theorem/Example.lean") -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source, encoding="utf-8")

    @staticmethod
    def claim(name: str, kind: str | None = None) -> str:
        attribute = f"@[tmio {kind}] " if kind is not None else ""
        return f"{attribute}theorem {name} : connection% (True) := by trivial\n"

    def assert_rejected(self) -> None:
        with self.assertRaises(classification.ClassificationError):
            classification.validate(self.root)

    def query(self, command: str, argument: str | None = None) -> str:
        output, errors = io.StringIO(), io.StringIO()
        arguments = [_TOOL.name, command] + ([argument] if argument is not None else [])
        with mock.patch.object(classification, "__file__", str(self.root / "tools" / _TOOL.name)), \
                mock.patch("sys.argv", arguments), \
                redirect_stdout(output), redirect_stderr(errors):
            result = classification.main()
        self.assertEqual(result, 0, errors.getvalue())
        self.assertEqual(errors.getvalue(), "")
        return output.getvalue()

    def test_all_five_explicit_categories_are_counted(self) -> None:
        self.write("".join(self.claim(f"claim_{kind}", kind)
                           for kind in ("T", "M", "TM", "MI", "IO")))
        self.assertEqual(
            classification.validate(self.root),
            {"T": 1, "M": 1, "TM": 1, "MI": 1, "IO": 1},
        )

    def test_missing_attribute_is_rejected(self) -> None:
        self.write(self.claim("missing"))
        self.assertEqual(classification.scan_connections(self.root)["missing"]["kinds"], [])
        self.assert_rejected()

    def test_new_unannotated_module_cannot_escape_preflight(self) -> None:
        self.write(self.claim("existing", "TM"))
        self.assertEqual(classification.validate(self.root)["TM"], 1)
        self.write(self.claim("new_connection"), "theorem/NewArea/NewModule.lean")
        with self.assertRaisesRegex(classification.ClassificationError, "new_connection"):
            classification.validate(self.root)

    def test_independent_i_o_and_other_invalid_categories_are_rejected(self) -> None:
        for kind in ("I", "O", "T-O", "translation", ""):
            with self.subTest(kind=kind):
                self.write(self.claim("invalid", kind))
                self.assert_rejected()

    def test_duplicate_attributes_are_rejected_even_when_they_agree(self) -> None:
        for first, second in (("TM", "TM"), ("TM", "MI")):
            for attributes in (
                f"@[tmio {first}, tmio {second}]",
                f"@[tmio {first}]\n@[tmio {second}]",
            ):
                with self.subTest(attributes=attributes):
                    self.write(attributes + "\n" + self.claim("duplicate"))
                    self.assertEqual(
                        classification.scan_connections(self.root)["duplicate"]["kinds"],
                        [first, second],
                    )
                    self.assert_rejected()

    def test_separate_legal_attribute_blocks_are_rejected(self) -> None:
        declarations = (
            self.claim("separate_blocks"),
            "theorem separate_blocks : True := by trivial\n",
            "private theorem separate_blocks : True := by trivial\n",
        )
        for declaration in declarations:
            for attributes in (
                "@[tmio TM]\n@[powerlib_domain]",
                "@[powerlib_domain]\n@[tmio TM]",
                "@[tmio TM] @[simp]",
                "@[tmio TM]\n/- A comment does not merge the blocks. -/\n@[simp]",
            ):
                with self.subTest(declaration=declaration, attributes=attributes):
                    self.write(self.claim("baseline", "TM") + attributes + "\n" + declaration)
                    entry = next(entry for entry in classification.scan_theorems(self.root).values()
                                 if entry["name"] == "separate_blocks")
                    self.assertEqual(entry["kinds"], ["TM"])
                    self.assertEqual(entry["attribute_block_count"], 2)
                    self.assert_rejected()

    def test_nonconnection_attribute_does_not_classify_next_declaration(self) -> None:
        self.write(
            "@[tmio T] theorem support : True := by trivial\n"
            + self.claim("missing")
        )
        entries = classification.scan_connections(self.root)
        self.assertEqual(set(entries), {"missing"})
        self.assertEqual(entries["missing"]["kinds"], [])
        self.assert_rejected()

    def test_attributed_nonconnections_are_allowed_but_not_counted_as_connections(self) -> None:
        self.write(
            "@[tmio T] theorem support : True := by trivial\n"
            + self.claim("published", "MI")
        )
        self.assertEqual(
            classification.validate(self.root),
            {"T": 0, "M": 0, "TM": 0, "MI": 1, "IO": 0},
        )
        self.assertEqual(set(classification.scan_classified(self.root)), {"support", "published"})

    def test_all_tagged_ordinary_and_private_theorems_are_discoverable(self) -> None:
        self.write(
            "namespace Reviewed\n"
            "@[tmio T] theorem theory : True := by trivial\n"
            "@[tmio M] lemma model : True := by trivial\n"
            "@[tmio M] private theorem helper : True := by trivial\n"
            "@[tmio IO] private theorem connection_helper : connection% (True) := by trivial\n"
            + self.claim("published", "TM")
            + "end Reviewed\n"
        )
        classified = classification.scan_classified(self.root)
        by_name = {entry["name"]: entry for entry in classified.values()}
        self.assertEqual(set(by_name), {
            "Reviewed.theory", "Reviewed.model", "Reviewed.helper",
            "Reviewed.connection_helper", "Reviewed.published",
        })
        self.assertEqual(by_name["Reviewed.theory"]["kinds"], ["T"])
        self.assertEqual(by_name["Reviewed.model"]["kinds"], ["M"])
        self.assertTrue(by_name["Reviewed.helper"]["private"])
        self.assertFalse(by_name["Reviewed.helper"]["connection"])
        self.assertTrue(by_name["Reviewed.connection_helper"]["private"])
        self.assertTrue(by_name["Reviewed.connection_helper"]["connection"])
        self.assertEqual(set(classification.scan_connections(self.root)), {"Reviewed.published"})
        self.assertEqual(
            classification.validate(self.root),
            {"T": 0, "M": 0, "TM": 1, "MI": 0, "IO": 0},
        )

    def test_unmarked_ordinary_and_private_theorems_remain_optional(self) -> None:
        self.write(
            "theorem ordinary : True := by trivial\n"
            "private theorem helper : True := by trivial\n"
            "private theorem connection_helper : connection% (True) := by trivial\n"
            + self.claim("published", "TM")
        )
        self.assertEqual(len(classification.scan_theorems(self.root)), 4)
        self.assertEqual(set(classification.scan_classified(self.root)), {"published"})
        self.assertEqual(classification.validate(self.root)["TM"], 1)

    def test_invalid_or_duplicate_tags_on_ordinary_and_private_theorems_fail(self) -> None:
        declarations = (
            "theorem invalid : True := by trivial\n",
            "private theorem invalid : True := by trivial\n",
            "private theorem invalid : connection% (True) := by trivial\n",
        )
        for declaration in declarations:
            for attribute in ("@[tmio I]", "@[tmio O]", "@[tmio T, tmio T]",
                              "@[tmio T]\n@[tmio M]"):
                with self.subTest(declaration=declaration, attribute=attribute):
                    self.write(self.claim("published", "TM") + attribute + "\n" + declaration)
                    self.assert_rejected()

    def test_cli_lists_and_shows_tagged_ordinary_and_private_theorems(self) -> None:
        self.write(
            "@[tmio T] theorem theory : True := by trivial\n"
            "@[tmio M] theorem model : True := by trivial\n"
            "@[tmio M] private theorem helper : True := by trivial\n"
            + self.claim("published", "TM")
        )
        self.assertIn("\ttheory\n", self.query("list", "T"))
        models = self.query("list", "M")
        self.assertIn("\tmodel\n", models)
        self.assertIn("\thelper (private)\n", models)
        self.assertNotIn("published", models)
        theory = json.loads(self.query("show", "theory"))
        self.assertEqual(theory["kinds"], ["T"])
        self.assertFalse(theory["connection"])
        helper = json.loads(self.query("show", "helper"))
        self.assertEqual(helper["kinds"], ["M"])
        self.assertTrue(helper["private"])

    def test_private_source_names_are_disambiguated_in_queries(self) -> None:
        self.write(self.claim("published", "TM"))
        self.write("@[tmio T] private theorem helper : True := by trivial\n", "theorem/First.lean")
        self.write("@[tmio M] private theorem helper : True := by trivial\n", "theorem/Second.lean")
        private = {key: entry for key, entry in classification.scan_classified(self.root).items()
                   if entry["private"]}
        self.assertEqual(len(private), 2)
        self.assertEqual({entry["module"] for entry in private.values()},
                         {"theorem.First", "theorem.Second"})
        matches = json.loads(self.query("show", "helper"))
        self.assertEqual(len(matches), 2)
        for key, entry in private.items():
            with self.subTest(key=key):
                self.assertEqual(json.loads(self.query("show", key)), entry)

    def test_cli_check_distinguishes_connection_and_tag_counts(self) -> None:
        self.write(
            "@[tmio T] theorem theory : True := by trivial\n"
            "@[tmio M] theorem model : True := by trivial\n"
            "@[tmio M] private theorem helper : True := by trivial\n"
            + self.claim("published", "TM")
        )
        output = self.query("check")
        self.assertIn("POWERLIB_TMIO_SOURCE_OK: 1 connection theorems; T 0, M 0, TM 1, MI 0, IO 0", output)
        self.assertIn("POWERLIB_TMIO_TAGS_OK: 4 classified theorems; T 1, M 2, TM 1, MI 0, IO 0", output)

    def test_private_connections_are_outside_public_preflight(self) -> None:
        self.write(
            "private theorem helper : connection% (True) := by trivial\n"
            + self.claim("published", "T")
        )
        self.assertEqual(set(classification.scan_connections(self.root)), {"published"})
        self.assertEqual(classification.validate(self.root)["T"], 1)

    def test_scanner_preserves_scope_lines_and_single_multiline_attribute_block(self) -> None:
        source = '''/- Outer comment
  /- @[tmio I] theorem nested_fake : connection% (True) := by trivial -/
  @[tmio O] theorem comment_fake : connection% (True) := by trivial
-/
def text := "@[tmio I] theorem string_fake : connection% (True) := by trivial"
namespace Outer
namespace Inner
section Context
variable (n : Nat)
/- Documentation before the single attribute block. -/
@[
  powerlib_domain,
  aesop (rule_sets := [A, B]),
  tmio TM,
  simp
]
theorem scoped (h : n = n) : connection% (n = n) := by trivial
end Context
@[tmio M, simp] lemma after_section : connection% (True) := by trivial
@[tmio IO] protected theorem protected_claim : connection% (True) := by trivial
@[tmio T] theorem _root_.Absolute.claim : connection% (True) := by trivial
end Inner
end Outer
-- @[tmio O] theorem line_fake : connection% (True) := by trivial
@[tmio MI] theorem outside : connection% (True) := by trivial
'''
        self.write(source, "theorem/Sub/Example.lean")
        entries = classification.scan_connections(self.root)
        expected = {
            "Outer.Inner.scoped": "TM",
            "Outer.Inner.after_section": "M",
            "Outer.Inner.protected_claim": "IO",
            "Absolute.claim": "T",
            "outside": "MI",
        }
        self.assertEqual(set(entries), set(expected))
        for name, kind in expected.items():
            with self.subTest(name=name):
                self.assertEqual(entries[name]["name"], name)
                self.assertEqual(entries[name]["kinds"], [kind])
                self.assertEqual(entries[name]["attribute_block_count"], 1)
                self.assertEqual(entries[name]["module"], "theorem.Sub.Example")
                self.assertEqual(entries[name]["path"], "theorem/Sub/Example.lean")
        self.assertEqual(
            entries["Outer.Inner.scoped"]["line"],
            source[:source.index("theorem scoped")].count("\n") + 1,
        )
        self.assertEqual(classification.validate(self.root), dict.fromkeys(expected.values(), 1))

    def test_duplicate_fully_qualified_declarations_are_rejected(self) -> None:
        source = "namespace Shared\n" + self.claim("duplicate", "TM") + "end Shared\n"
        self.write(source, "theorem/First.lean")
        self.write(source, "theorem/Second.lean")
        self.assert_rejected()

    def test_empty_inventory_is_not_reported_as_success(self) -> None:
        self.write("-- No published connections.\n")
        self.assert_rejected()

    def test_unterminated_attribute_is_rejected(self) -> None:
        self.write("@[tmio TM\n" + self.claim("unclosed"))
        self.assert_rejected()


if __name__ == "__main__":
    unittest.main()
