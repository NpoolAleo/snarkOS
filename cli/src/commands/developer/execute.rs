// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkOS library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::{CurrentNetwork, Developer};

use anyhow::{anyhow, bail, ensure, Result};
use clap::Parser;
use colored::Colorize;
use snarkvm::{
    ledger::Execution,
    prelude::{
        query::Query,
        store::{helpers::memory::ConsensusMemory, ConsensusStore},
        Address, Authorization, Identifier, Locator, PrivateKey, Process, ProgramID, Transaction, Value, VM,
    },
    synthesizer::execution_cost,
};

use std::str::FromStr;
use zeroize::Zeroize;

/// Executes an Aleo program function.
#[derive(Debug, Parser)]
pub struct Execute {
    /// The program identifier.
    program_id: ProgramID<CurrentNetwork>,
    /// The function name.
    function: Identifier<CurrentNetwork>,
    /// The function inputs.
    inputs: Vec<Value<CurrentNetwork>>,
    /// The private key used to generate the execution.
    #[clap(short, long)]
    private_key: String,
    /// The endpoint to query node state from.
    #[clap(short, long)]
    query: String,
    /// The priority fee in microcredits.
    #[clap(long)]
    priority_fee: Option<u64>,
    /// The record to spend the fee from.
    #[clap(short, long)]
    record: Option<String>,
    /// The endpoint used to broadcast the generated transaction.
    #[clap(short, long, conflicts_with = "dry_run")]
    broadcast: Option<String>,
    /// Performs a dry-run of transaction generation.
    #[clap(short, long, conflicts_with = "broadcast")]
    dry_run: bool,
    /// Store generated deployment transaction to a local file.
    #[clap(long)]
    store: Option<String>,
}

impl Drop for Execute {
    /// Zeroize the private key when the `Execute` struct goes out of scope.
    fn drop(&mut self) {
        self.private_key.zeroize();
    }
}

impl Execute {
    /// Executes an Aleo program function with the provided inputs.
    #[allow(clippy::format_in_format_args)]
    pub fn parse(self) -> Result<String> {
        // Ensure that the user has specified an action.
        if !self.dry_run && self.broadcast.is_none() && self.store.is_none() {
            bail!("❌ Please specify one of the following actions: --broadcast, --dry-run, --store");
        }

        // Specify the query
        let query = Query::from(&self.query);

        // Retrieve the private key.
        let private_key = PrivateKey::from_str(&self.private_key)?;

        let locator = Locator::<CurrentNetwork>::from_str(&format!("{}/{}", self.program_id, self.function))?;
        println!("📦 Creating execution transaction for '{}'...\n", &locator.to_string().bold());
        // Generate the execution transaction.
        let transaction = {
            // Initialize an RNG.
            let rng = &mut rand::thread_rng();

            // Initialize the VM.
            let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
            let vm = VM::from(store)?;

            // // Load the program and it's imports into the process.
            // load_program(&self.query, &mut vm.process().write(), &self.program_id)?;

            // Create a new transaction.
            vm.execute(&private_key, (self.program_id, self.function), self.inputs.iter(), None, 0, Some(query), rng)?
        };

        // Check if the public balance is sufficient.
        if self.record.is_none() {
            // Fetch the public balance.
            let address = Address::try_from(&private_key)?;
            let public_balance = Developer::get_public_balance(&address, &self.query)?;

            // Check if the public balance is sufficient.
            let storage_cost = transaction
                .execution()
                .ok_or_else(|| anyhow!("The transaction does not contain an execution"))?
                .size_in_bytes()?;

            // Calculate the base fee.
            // This fee is the minimum fee required to pay for the transaction,
            // excluding any finalize fees that the execution may incur.
            let base_fee = storage_cost.saturating_add(self.priority_fee.unwrap_or(0));

            // If the public balance is insufficient, return an error.
            if public_balance < base_fee {
                bail!(
                    "❌ The public balance of {} is insufficient to pay the base fee for `{}`",
                    public_balance,
                    locator.to_string().bold()
                );
            }
        }

        println!("✅ Created execution transaction for '{}'", locator.to_string().bold());

        // Determine if the transaction should be broadcast, stored, or displayed to the user.
        Developer::handle_transaction(&self.broadcast, self.dry_run, &self.store, transaction, locator.to_string())
    }

    /// Executes an Aleo program function with the provided inputs.
    #[allow(clippy::format_in_format_args)]
    pub fn parse_all(self) -> Result<String> {
        // Ensure that the user has specified an action.
        if !self.dry_run && self.broadcast.is_none() && self.store.is_none() {
            bail!("❌ Please specify one of the following actions: --broadcast, --dry-run, --store");
        }

        // Specify the query
        let query = Query::from(&self.query);

        // Retrieve the private key.
        let private_key = PrivateKey::from_str(&self.private_key)?;

        let locator = Locator::<CurrentNetwork>::from_str(&format!("{}/{}", self.program_id, self.function))?;
        println!("📦 Creating execution transaction for '{}'...\n", &locator.to_string().bold());
        // Generate the execution transaction.

        // Generate the execution transaction.
        let transaction = {
            // Initialize an RNG.
            let rng = &mut rand::thread_rng();

            // Initialize the VM.
            let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
            let vm = VM::from(store)?;

            // Load the program and it's imports into the process.
            load_program(&self.query, &mut vm.process().write(), &self.program_id)?;

            // Prepare the fee.
            let fee_record = match &self.record {
                Some(record_string) => Some(Developer::parse_record(&private_key, record_string)?),
                None => None,
            };
            let (program_id, function_name) = (self.program_id, self.function);
            // Compute the authorization.
            let authorization = vm.authorize(&private_key, program_id, function_name, self.inputs.iter(), rng)?;
            // Determine if a fee is required.
            let is_fee_required = !authorization.is_split();
            let priority_fee_in_microcredits = 0;
            // Determine if a priority fee is declared.
            let is_priority_fee_declared = priority_fee_in_microcredits > 0;
            // Compute the execution.
            let execution = vm.execute_authorization_raw(authorization, Some(query.clone()), rng)?;
            // Compute the fee.
            let fee = match is_fee_required || is_priority_fee_declared {
                true => {
                    // Compute the minimum execution cost.
                    let (minimum_execution_cost, (_, _)) = execution_cost(&vm, &execution)?;
                    // Compute the execution ID.
                    let execution_id = execution.to_execution_id()?;
                    // Authorize the fee.
                    let authorization = match fee_record {
                        Some(record) => vm.authorize_fee_private(
                            &private_key,
                            record,
                            minimum_execution_cost,
                            priority_fee_in_microcredits,
                            execution_id,
                            rng,
                        )?,
                        None => vm.authorize_fee_public(
                            &private_key,
                            minimum_execution_cost,
                            priority_fee_in_microcredits,
                            execution_id,
                            rng,
                        )?,
                    };
                    // Execute the fee.
                    Some(vm.execute_fee_authorization_raw(authorization, Some(query.clone()), rng)?)
                }
                false => None,
            };
            // Return the execute transaction.
            Transaction::from_execution(execution, fee)?
        };

        // Check if the public balance is sufficient.
        if self.record.is_none() {
            // Fetch the public balance.
            let address = Address::try_from(&private_key)?;
            let public_balance = Developer::get_public_balance(&address, &self.query)?;

            // Check if the public balance is sufficient.
            let storage_cost = transaction
                .execution()
                .ok_or_else(|| anyhow!("The transaction does not contain an execution"))?
                .size_in_bytes()?;

            // Calculate the base fee.
            // This fee is the minimum fee required to pay for the transaction,
            // excluding any finalize fees that the execution may incur.
            let base_fee = storage_cost.saturating_add(self.priority_fee.unwrap_or(0));

            // If the public balance is insufficient, return an error.
            if public_balance < base_fee {
                bail!(
                    "❌ The public balance of {} is insufficient to pay the base fee for `{}`",
                    public_balance,
                    locator.to_string().bold()
                );
            }
        }

        println!("✅ Created execution transaction for '{}'", locator.to_string().bold());

        // Determine if the transaction should be broadcast, stored, or displayed to the user.
        Developer::handle_transaction(&self.broadcast, self.dry_run, &self.store, transaction, locator.to_string())
    }
}

pub struct SphinxTx {}

impl SphinxTx {
    const PROGRAM_ID: &'static str = "credits.aleo";
    const FUNCTION: &'static str = "transfer_public";
    const LOCATOR: &'static str = "credits.aleo/transfer_public";

    pub fn sign1(private_key: &str, to: &str, amount: &str) -> Result<Authorization<CurrentNetwork>> {
        // Initialize an RNG.
        let rng = &mut rand::thread_rng();

        // Initialize the VM.
        let store: ConsensusStore<snarkvm::prelude::Testnet3, ConsensusMemory<snarkvm::prelude::Testnet3>> =
            ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
        let vm: VM<snarkvm::prelude::Testnet3, ConsensusMemory<snarkvm::prelude::Testnet3>> = VM::from(store.clone())?;

        // // Load the program and it's imports into the process.
        // load_program(&self.query, &mut vm.process().write(), &self.program_id)?;
        // Retrieve the private key.
        let private_key = PrivateKey::from_str(private_key)?;
        let (program_id, function_name) = (SphinxTx::PROGRAM_ID, SphinxTx::FUNCTION);
        let inputs = vec![to, amount];
        // Compute the authorization.
        vm.authorize(&private_key, program_id, function_name, inputs, rng)
    }

    pub fn plugin2(endpoint: &str, authorization: Authorization<CurrentNetwork>) -> Result<Execution<CurrentNetwork>> {
        // Specify the query
        let query = Query::from(endpoint);

        println!("📦 Creating execution transaction for '{}'...\n", &SphinxTx::LOCATOR.bold());

        // Check if the public balance is sufficient.
        // Fetch the public balance.
        let from =
            Address::<CurrentNetwork>::from_str("aleo1rhgdu77hgyqd3xjj8ucu3jj9r2krwz6mnzyd80gncr5fxcwlh5rsvzp9px")?;
        let public_balance = Developer::get_public_balance(&from, endpoint)?;

        // base fee,That's it for now
        let base_fee = 1388;
        // If the public balance is insufficient, return an error.
        if public_balance < base_fee {
            bail!(
                "❌ The public balance of {} is insufficient to pay the base fee for `{}`",
                public_balance,
                SphinxTx::LOCATOR.bold()
            );
        }

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();
        // Initialize the VM.
        let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
        let vm: VM<snarkvm::prelude::Testnet3, ConsensusMemory<snarkvm::prelude::Testnet3>> = VM::from(store.clone())?;

        // Compute the execution.
        vm.execute_authorization_raw(authorization, Some(query.clone()), rng)
    }

    pub fn sign3(private_key: &str, execution: Execution<CurrentNetwork>) -> Result<Authorization<CurrentNetwork>> {
        // Initialize an RNG.
        let rng = &mut rand::thread_rng();
        // Initialize the VM.
        let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
        let vm: VM<snarkvm::prelude::Testnet3, ConsensusMemory<snarkvm::prelude::Testnet3>> = VM::from(store.clone())?;

        let (minimum_execution_cost, (_, _)) = execution_cost(&vm, &execution)?;

        // Compute the execution ID.
        let execution_id = execution.to_execution_id()?;
        let private_key = PrivateKey::from_str(private_key)?;
        vm.authorize_fee_public(&private_key, minimum_execution_cost, 0, execution_id, rng)
    }

    pub fn broadcast_transaction(
        endpoint: &str,
        broadcast: String,
        authorization: Authorization<CurrentNetwork>,
        execution: Execution<CurrentNetwork>,
    ) -> Result<String> {
        // Specify the query
        let query = Query::from(endpoint);

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();
        // Initialize the VM.
        let store = ConsensusStore::<CurrentNetwork, ConsensusMemory<CurrentNetwork>>::open(None)?;
        let vm: VM<snarkvm::prelude::Testnet3, ConsensusMemory<snarkvm::prelude::Testnet3>> = VM::from(store.clone())?;

        // Execute the fee.
        let fee = Some(vm.execute_fee_authorization_raw(authorization, Some(query.clone()), rng)?);

        // Return the execute transaction.
        let transaction = Transaction::from_execution(execution, fee)?;

        // Get the transaction id.
        let transaction_id = transaction.id();

        // Ensure the transaction is not a fee transaction.
        ensure!(!transaction.is_fee(), "The transaction is a fee transaction and cannot be broadcast");
        if let Transaction::Execute(..) = transaction {
            match ureq::post(&broadcast).send_json(&transaction) {
                Ok(id) => {
                    // Remove the quotes from the response.
                    let response_string = id.into_string()?.trim_matches('\"').to_string();
                    ensure!(
                        response_string == transaction_id.to_string(),
                        "The response does not match the transaction id. ({response_string} != {transaction_id})"
                    );
                }
                Err(error) => bail!(error),
            };
        } else {
            bail!("failed to broadcast transaction:{}", transaction_id.to_string())
        };
        // Output the transaction id.
        Ok(transaction_id.to_string())
    }

    pub fn sync_transaction(sync: String, transaction_id: String) -> Result<Option<String>> {
        match ureq::get(&format!("{sync}/transaction/{transaction_id}")).call() {
            Ok(resp) => {
                // if resp != None {}
                println!("success: {:#?}", resp);
                Ok(None)
            }
            Err(error) => {
                println!("error: {:#?}", error);
                bail!(error)
            }
        }
    }
}

/// A helper function to recursively load the program and all of its imports into the process.
fn load_program(
    endpoint: &str,
    process: &mut Process<CurrentNetwork>,
    program_id: &ProgramID<CurrentNetwork>,
) -> Result<()> {
    // Fetch the program.
    let program = Developer::fetch_program(program_id, endpoint)?;

    // Return early if the program is already loaded.
    if process.contains_program(program.id()) {
        return Ok(());
    }

    // Iterate through the program imports.
    for import_program_id in program.imports().keys() {
        // Add the imports to the process if does not exist yet.
        if !process.contains_program(import_program_id) {
            // Recursively load the program and its imports.
            load_program(endpoint, process, import_program_id)?;
        }
    }

    // Add the program to the process if it does not already exist.
    if !process.contains_program(program.id()) {
        process.add_program(&program)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::{Command, CLI};
    use std::{thread, time};

    extern crate serde;
    extern crate serde_json;

    #[test]
    fn clap_snarkos_execute() {
        let arg_vec = vec![
            "snarkos",
            "developer",
            "execute",
            "--private-key",
            "PRIVATE_KEY",
            "--query",
            "QUERY",
            "--priority-fee",
            "77",
            "--record",
            "RECORD",
            "hello.aleo",
            "hello",
            "1u32",
            "2u32",
        ];
        let cli = CLI::parse_from(arg_vec);

        if let Command::Developer(Developer::Execute(execute)) = cli.command {
            assert_eq!(execute.private_key, "PRIVATE_KEY");
            assert_eq!(execute.query, "QUERY");
            assert_eq!(execute.priority_fee, Some(77));
            assert_eq!(execute.record, Some("RECORD".into()));
            assert_eq!(execute.program_id, "hello.aleo".try_into().unwrap());
            assert_eq!(execute.function, "hello".try_into().unwrap());
            assert_eq!(execute.inputs, vec!["1u32".try_into().unwrap(), "2u32".try_into().unwrap()]);
        } else {
            panic!("Unexpected result of clap parsing!");
        }
    }

    #[test]
    fn test_execute_tx() {
        let arg_vec = vec![
            "snarkos",
            "developer",
            "execute",
            "--private-key",
            "APrivateKey1zkp8CZNn3yeCseEtxuVPbDCwSyhGW6yZKUYKfgXmcpoGPWH",
            "--query",
            "http://10.1.7.110:3030",
            "credits.aleo",
            "transfer_public",
            "aleo19rdamt5rmn8w20psejsat5wrxfh0u7dq7sxtn84phhh0jhqka5qsqnkuzk",
            "500001u64",
            "--broadcast",
            "http://10.1.7.110:3030/testnet3/transaction/broadcast",
        ];
        let cli = CLI::parse_from(arg_vec);

        if let Command::Developer(Developer::Execute(execute)) = cli.command {
            let _ = execute.parse();
        } else {
            panic!("Unexpected result of clap parsing!");
        }
    }

    #[test]
    fn test_sphinx_tx() {
        fn _test_sphinx_tx() -> Result<String> {
            let net_name = "testnet3";
            let endpoint = "http://10.1.7.110:3030";
            let private_key = "APrivateKey1zkp8CZNn3yeCseEtxuVPbDCwSyhGW6yZKUYKfgXmcpoGPWH";
            let to: &str = "aleo19rdamt5rmn8w20psejsat5wrxfh0u7dq7sxtn84phhh0jhqka5qsqnkuzk";
            let amount = "500001u64";

            let authorization = SphinxTx::sign1(private_key, to, amount)?;

            let serialized = serde_json::to_string(&authorization).unwrap();
            let authorization = serde_json::from_str(&serialized).unwrap();

            let execution = SphinxTx::plugin2(endpoint, authorization)?;

            let serialized = serde_json::to_string(&execution).unwrap();
            let execution: Execution<CurrentNetwork> = serde_json::from_str(&serialized).unwrap();

            let authorization = SphinxTx::sign3(private_key, execution.clone())?;

            let serialized = serde_json::to_string(&authorization).unwrap();
            let authorization = serde_json::from_str(&serialized).unwrap();

            println!("✅ Created execution transaction for '{}'", SphinxTx::LOCATOR.bold());

            let transaction_id = SphinxTx::broadcast_transaction(
                endpoint,
                format!("{}/{}/{}", endpoint, net_name, "transaction/broadcast"),
                authorization,
                execution,
            )?;

            let mut index = 0;
            while index < 5 {
                index += 1;
                let _ = SphinxTx::sync_transaction(format!("{}/{}", endpoint, net_name), transaction_id.to_string());
                let ten_millis = time::Duration::from_secs(60);
                thread::sleep(ten_millis)
            }

            Ok(transaction_id.to_string())
        }

        let _ = _test_sphinx_tx();
        // Determine if the transaction should be broadcast, stored, or displayed to the user.
        // Developer::handle_transaction(&self.broadcast, self.dry_run, &self.store, transaction, LOCATOR.to_string())
    }
}
