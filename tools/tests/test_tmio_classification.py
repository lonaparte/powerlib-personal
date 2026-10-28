"""Regression tests for the source preflight, without Lean or repository edits."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import tempfile
import unittest


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

    def test_nonconnection_attribute_does_not_classify_next_declaration(self) -> None:
        self.write(
            "@[tmio T] theorem support : True := by trivial\n"
            + self.claim("missing")
        )
        entries = classification.scan_connections(self.root)
        self.assertEqual(set(entries), {"missing"})
        self.assertEqual(entries["missing"]["kinds"], [])
        self.assert_rejected()

    def test_attributed_nonconnections_are_allowed_and_not_counted(self) -> None:
        self.write(
            "@[tmio T] theorem support : True := by trivial\n"
            + self.claim("published", "MI")
        )
        self.assertEqual(
            classification.validate(self.root),
            {"T": 0, "M": 0, "TM": 0, "MI": 1, "IO": 0},
        )

    def test_private_connections_are_outside_public_preflight(self) -> None:
        self.write(
            "private theorem helper : connection% (True) := by trivial\n"
            + self.claim("published", "T")
        )
        self.assertEqual(set(classification.scan_connections(self.root)), {"published"})
        self.assertEqual(classification.validate(self.root)["T"], 1)

    def test_scanner_preserves_scope_lines_and_adjacent_multiline_attributes(self) -> None:
        source = '''/- Outer comment
  /- @[tmio I] theorem nested_fake : connection% (True) := by trivial -/
  @[tmio O] theorem comment_fake : connection% (True) := by trivial
-/
def text := "@[tmio I] theorem string_fake : connection% (True) := by trivial"
namespace Outer
namespace Inner
section Context
variable (n : Nat)
@[powerlib_domain]
/- Documentation between attribute blocks. -/
@[
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
