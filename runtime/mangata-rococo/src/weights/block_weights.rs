// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-10-13 (Y/M/D)
//! HOSTNAME: `thinkpad`, CPU: `AMD Ryzen 7 PRO 4750U with Radeon Graphics`
//!
//! SHORT-NAME: `block`, LONG-NAME: `BlockExecution`, RUNTIME: `Mangata Development`
//! WARMUPS: `10`, REPEAT: `100`
//! WEIGHT-PATH: ``
//! WEIGHT-METRIC: `Average`, WEIGHT-MUL: `1.0`, WEIGHT-ADD: `0`

// Executed Command:
//   target/release/mangata-node
//   benchmark
//   overhead
//   --execution
//   native
//   --chain
//   dev
//   -l
//   info

use frame_support::{
	parameter_types,
	weights::{constants::WEIGHT_PER_NANOS, constants::WEIGHT_PER_MILLIS, Weight},
};

parameter_types! {
	/// Time to execute an empty block.
	/// Calculated by multiplying the *Average* with `1.0` and adding `0`.
	///
	/// Stats nanoseconds:
	///   Min, Max: 76_228_274, 78_691_308
	///   Average:  76_453_434
	///   Median:   76_401_337
	///   Std-Dev:  257659.68
	///
	/// Percentiles nanoseconds:
	///   99th: 76_934_073
	///   95th: 76_658_627
	///   75th: 76_494_992
	pub const BlockExecutionWeight: Weight = 12 * WEIGHT_PER_MILLIS;
}

#[cfg(test)]
mod test_weights {
	use frame_support::weights::constants;

	/// Checks that the weight exists and is sane.
	// NOTE: If this test fails but you are sure that the generated values are fine,
	// you can delete it.
	#[test]
	fn sane() {
		let w = super::BlockExecutionWeight::get();

		// At least 100 µs.
		assert!(w >= 100 * constants::WEIGHT_PER_MICROS, "Weight should be at least 100 µs.");
		// At most 50 ms.
		assert!(w <= 50 * constants::WEIGHT_PER_MILLIS, "Weight should be at most 50 ms.");
	}
}