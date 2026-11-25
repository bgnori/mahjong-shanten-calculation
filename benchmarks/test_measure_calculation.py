import json
from pathlib import Path
import subprocess
import sys
import unittest


MEASURE = Path(__file__).with_name("measure_calculation.py")
RESULT = "SHANTEN_RESULT operation=mentsu case=test result=some 0 calculation_ns=1000000"


class CalculationMeasureTests(unittest.TestCase):
    def run_measure(self, startup_timeout, calculation_timeout, program):
        return subprocess.run(
            [sys.executable, str(MEASURE), "--startup-timeout", str(startup_timeout),
             "--calculation-timeout", str(calculation_timeout), "--max-memory-mib", "256",
             "--", sys.executable, "-u", "-c", program],
            capture_output=True, text=True, check=False,
        )

    def test_slow_startup_does_not_consume_calculation_timeout(self):
        result = self.run_measure(
            3, 0.3,
            "import time; time.sleep(0.5); print('SHANTEN_READY', flush=True); "
            f"assert input() == 'RUN'; print({RESULT!r}, flush=True)",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        metrics = json.loads(result.stdout)
        self.assertEqual(metrics["status"], "success")
        self.assertGreater(metrics["startup_elapsed_seconds"], 0.3)
        self.assertEqual(metrics["calculation_ns"], 1_000_000)

    def test_calculation_timeout_starts_after_handshake(self):
        result = self.run_measure(
            3, 0.1,
            "import time; print('SHANTEN_READY', flush=True); "
            "assert input() == 'RUN'; time.sleep(2)",
        )
        self.assertEqual(result.returncode, 124)
        metrics = json.loads(result.stdout)
        self.assertEqual(metrics["status"], "calculation_timeout")
        self.assertIsNotNone(metrics["startup_elapsed_seconds"])
        self.assertGreaterEqual(metrics["calculation_wall_seconds"], 0.1)
        self.assertIsNone(metrics["calculation_ns"])

    def test_startup_timeout_is_distinct(self):
        result = self.run_measure(0.1, 3, "import time; time.sleep(2)")
        self.assertEqual(result.returncode, 124)
        metrics = json.loads(result.stdout)
        self.assertEqual(metrics["status"], "startup_timeout")
        self.assertGreaterEqual(metrics["startup_elapsed_seconds"], 0.1)
        self.assertIsNone(metrics["calculation_ns"])

    def test_process_failure_is_not_a_timeout_or_success(self):
        result = self.run_measure(3, 3, "import sys; sys.exit(7)")
        self.assertEqual(result.returncode, 1)
        metrics = json.loads(result.stdout)
        self.assertEqual(metrics["status"], "startup_failure")

    def test_invalid_result_is_rejected(self):
        result = self.run_measure(
            3, 3, "print('SHANTEN_READY', flush=True); "
            "assert input() == 'RUN'; print('SHANTEN_RESULT invalid', flush=True)",
        )
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)["status"], "invalid_result")

    def test_failure_after_result_is_not_success(self):
        result = self.run_measure(
            3, 3, "import sys; print('SHANTEN_READY', flush=True); "
            f"assert input() == 'RUN'; print({RESULT!r}, flush=True); sys.exit(7)",
        )
        self.assertEqual(result.returncode, 1)
        metrics = json.loads(result.stdout)
        self.assertEqual(metrics["status"], "process_failure")
        self.assertEqual(metrics["exit_code"], 7)

    def test_reported_calculation_cannot_exceed_limit_on_success(self):
        slow_result = RESULT.replace("1000000", "3000000000")
        result = self.run_measure(
            3, 0.5, "print('SHANTEN_READY', flush=True); "
            f"assert input() == 'RUN'; print({slow_result!r}, flush=True)",
        )
        self.assertEqual(result.returncode, 124)
        self.assertEqual(json.loads(result.stdout)["status"], "calculation_timeout")


if __name__ == "__main__":
    unittest.main()
