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

//! Autogenerated weights for pallet_treasury
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-09-16, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// /home/ubuntu/mangata-node/scripts/..//target/release/mangata-node
// benchmark
// pallet
// --chain
// dev
// --execution
// wasm
// --wasm-execution
// compiled
// --pallet
// pallet_treasury
// --extrinsic
// *
// --steps
// 50
// --repeat
// 20
// --output
// ./benchmarks/pallet_treasury_weights.rs
// --template
// ./templates/module-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(clippy::unnecessary_cast)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_treasury.
pub trait WeightInfo {
	fn propose_spend() -> Weight;
	fn reject_proposal() -> Weight;
	fn approve_proposal(p: u32, ) -> Weight;
	fn remove_approval() -> Weight;
	fn on_initialize_proposals(p: u32, ) -> Weight;
}

/// Weights for pallet_treasury using the Mangata node and recommended hardware.
pub struct ModuleWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_treasury::WeightInfo for ModuleWeight<T> {
	fn spend() -> Weight { (Weight::from_ref_time(34_972_000))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(3 as u64))
		}
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: Treasury ProposalCount (r:1 w:1)
	// Storage: Treasury Proposals (r:0 w:1)
	fn propose_spend() -> Weight {
		(Weight::from_ref_time(35_210_000))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(3 as u64))
	}
	// Storage: Treasury Proposals (r:1 w:1)
	// Storage: Tokens Accounts (r:1 w:1)
	// Storage: Tokens TotalIssuance (r:1 w:1)
	fn reject_proposal() -> Weight {
		(Weight::from_ref_time(33_577_000))
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(3 as u64))
	}
	// Storage: Treasury Proposals (r:1 w:0)
	// Storage: Treasury Approvals (r:1 w:1)
	fn approve_proposal(p: u32, ) -> Weight {
		(Weight::from_ref_time(12_461_000))
			// Standard Error: 0
			.saturating_add((Weight::from_ref_time(172_000)).saturating_mul(p as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: Treasury Approvals (r:1 w:1)
	fn remove_approval() -> Weight {
		(Weight::from_ref_time(6_937_000))
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: Tokens Accounts (r:1 w:0)
	// Storage: Treasury Approvals (r:1 w:1)
	// Storage: Tokens TotalIssuance (r:1 w:1)
	// Storage: Treasury Proposals (r:2 w:0)
	fn on_initialize_proposals(p: u32, ) -> Weight {
		(Weight::from_ref_time(26_021_000))
			// Standard Error: 4_000
			.saturating_add((Weight::from_ref_time(4_225_000)).saturating_mul(p as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().reads((1 as u64).saturating_mul(p as u64)))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn propose_spend() -> Weight {
		(Weight::from_ref_time(35_210_000))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(3 as u64))
	}
	fn reject_proposal() -> Weight {
		(Weight::from_ref_time(33_577_000))
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(3 as u64))
	}
	fn approve_proposal(p: u32, ) -> Weight {
		(Weight::from_ref_time(12_461_000))
			// Standard Error: 0
			.saturating_add((Weight::from_ref_time(172_000)).saturating_mul(p as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn remove_approval() -> Weight {
		(Weight::from_ref_time(6_937_000))
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	fn on_initialize_proposals(p: u32, ) -> Weight {
		(Weight::from_ref_time(26_021_000))
			// Standard Error: 4_000
			.saturating_add((Weight::from_ref_time(4_225_000)).saturating_mul(p as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().reads((1 as u64).saturating_mul(p as u64)))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
}
