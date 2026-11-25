import json
from pathlib import Path
import subprocess
import sys
import unittest


MEASURE = Path(__file__).with_name("measure.py")


class MeasureTests(unittest.TestCase):
    def run_measure(self, timeout, program):
        return subprocess.run(
            [sys.executable, str(MEASURE), "--timeout", str(timeout),
             "--max-memory-mib", "256", "--", sys.executable, "-c", program],
            capture_output=True, text=True, check=False,
        )

    def test_success_reports_output_and_metrics(self):
        result = self.run_measure(5, "print('hello', end='')")
        self.assertEqual(result.returncode, 0)
        lines = result.stdout.splitlines()
        self.assertEqual(lines[0], "hello")
        metrics = json.loads(lines[-1])
        self.assertEqual(metrics["exit_code"], 0)
        self.assertFalse(metrics["timed_out"])
        self.assertGreater(metrics["max_rss_kib"], 0)

    def test_failure_is_not_reported_as_success(self):
        result = self.run_measure(5, "import sys; sys.exit(7)")
        self.assertEqual(result.returncode, 7)
        self.assertEqual(json.loads(result.stdout)["exit_code"], 7)

    def test_timeout_is_recorded_and_propagated(self):
        result = self.run_measure(0.1, "import time; time.sleep(2)")
        self.assertEqual(result.returncode, 124)
        self.assertTrue(json.loads(result.stdout)["timed_out"])

    def test_memory_limit_failure_is_reported(self):
        result = self.run_measure(5, "data = bytearray(512 * 1024 * 1024)")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(json.loads(result.stdout)["timed_out"])
        self.assertIn("MemoryError", result.stderr)


if __name__ == "__main__":
    unittest.main()
