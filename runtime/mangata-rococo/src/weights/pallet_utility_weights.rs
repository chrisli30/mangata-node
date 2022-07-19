// This file is part of Mangata.

// Copyright (C) 2020-2022 Mangata Foundation.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Autogenerated weights for pallet_utility
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-07-03, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// /home/ubuntu/mangata-node/scripts/..//target/release/mangata-node
// benchmark
// --chain
// dev
// --execution
// wasm
// --wasm-execution
// compiled
// --pallet
// pallet_utility
// --extrinsic
// *
// --steps
// 50
// --repeat
// 20
// --output
// ./benchmarks/pallet_utility_weights.rs
// --template
// ./templates/module-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(clippy::unnecessary_cast)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_utility.
pub trait WeightInfo {
	fn batch(c: u32, ) -> Weight;
	fn as_derivative() -> Weight;
	fn batch_all(c: u32, ) -> Weight;
	fn dispatch_as() -> Weight;
	fn force_batch(c: u32, ) -> Weight;
}

/// Weights for pallet_utility using the Mangata node and recommended hardware.
pub struct ModuleWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_utility::WeightInfo for ModuleWeight<T> {
	fn batch(c: u32, ) -> Weight {
		(16_300_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((5_521_000 as Weight).saturating_mul(c as Weight))
	}
	fn as_derivative() -> Weight {
		(4_121_000 as Weight)
	}
	fn batch_all(c: u32, ) -> Weight {
		(27_294_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((5_961_000 as Weight).saturating_mul(c as Weight))
	}
	fn dispatch_as() -> Weight {
		(13_142_000 as Weight)
	}
	/// The range of component `c` is `[0, 1000]`.
	fn force_batch(c: u32, ) -> Weight {
		(19_136_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((2_697_000 as Weight).saturating_mul(c as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn batch(c: u32, ) -> Weight {
		(16_300_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((5_521_000 as Weight).saturating_mul(c as Weight))
	}
	fn as_derivative() -> Weight {
		(4_121_000 as Weight)
	}
	fn batch_all(c: u32, ) -> Weight {
		(27_294_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((5_961_000 as Weight).saturating_mul(c as Weight))
	}
	fn dispatch_as() -> Weight {
		(13_142_000 as Weight)
	}
	/// The range of component `c` is `[0, 1000]`.
	fn force_batch(c: u32, ) -> Weight {
		(19_136_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((2_697_000 as Weight).saturating_mul(c as Weight))
	}
}