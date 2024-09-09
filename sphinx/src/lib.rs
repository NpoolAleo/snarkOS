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
use anyhow::{anyhow, bail, ensure, Result};
use colored::Colorize;
use core::str::FromStr;
use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use snarkvm::{
    console::{
        account::PrivateKey,
        prelude::{Environment, Uniform},
        types::Field,
    },
    ledger::Execution,
    prelude::{
        Network,
        query::Query,
        store::{helpers::memory::ConsensusMemory, ConsensusStore},
        Address, Authorization, Literal, Plaintext, Transaction, Value, VM,
    },
    synthesizer::process::execution_cost,
};

pub fn new_account<N: Network>(seed: Option<String>) -> Result<snarkos_account::Account<N>> {
    // Recover the seed.
    let seed = match seed {
        // Recover the field element deterministically.
        Some(seed) => Field::new(
            <N as Environment>::Field::from_str(&seed).map_err(|e| anyhow!("Invalid seed - {e}"))?,
        ),
        // Sample a random field element.
        None => Field::rand(&mut ChaChaRng::from_entropy()),
    };
    // Recover the private key from the seed as a field element.
    let private_key =
        PrivateKey::try_from(seed).map_err(|_| anyhow!("Failed to convert the seed into a valid private key"))?;
    // Construct the account.
    let account = snarkos_account::Account::<N>::try_from(private_key)?;
    Ok(account)
}


pub fn check_pub_address<N: Network>(pub_addr: &str) -> Result<Address<N>> {
    let pubaddr = Address::<N>::from_str(pub_addr)?;
    Ok(pubaddr)
}

pub struct SphinxTx {
}

impl SphinxTx {
    const PROGRAM_ID: &'static str = "credits.aleo";
    const FUNCTION: &'static str = "transfer_public";
    const LOCATOR: &'static str = "credits.aleo/transfer_public";

    pub fn gen_tx_authorization<N: Network>(private_key: &str, to: &str, amount: &str) -> Result<Authorization<N>> {
        // Initialize an RNG.
        let rng = &mut rand::thread_rng();

        // Initialize the VM.
        let store: ConsensusStore<N, ConsensusMemory<N>> =
            ConsensusStore::<N, ConsensusMemory<N>>::open(None)?;
        let vm: VM<N, ConsensusMemory<N>> = VM::from(store.clone())?;

        // // Load the program and it's imports into the process.
        // Retrieve the private key.
        let private_key = PrivateKey::from_str(private_key)?;
        let (program_id, function_name) = (SphinxTx::PROGRAM_ID, SphinxTx::FUNCTION);
        let inputs = vec![to, amount];
        // Compute the authorization.
        vm.authorize(&private_key, program_id, function_name, inputs, rng)
    }

    pub fn gen_tx_execution<N: Network>(
        endpoint: &str,
        from: &str,
        authorization: Authorization<N>,
    ) -> Result<Execution<N>> {
        // Specify the query
        let query = Query::from(endpoint);

        // Check if the public balance is sufficient.
        // Fetch the public balance.
        let public_balance = SphinxTx::get_public_balance::<N>(from, endpoint)?;
        println!("balancecccccc:{public_balance}");
        // base fee,That's it for now
        let base_fee = 1388;
        // If the public balance is insufficient, return an error.
        if public_balance < base_fee {
            bail!(
                "the public balance {} is insufficient to pay the base fee for `{}`",
                public_balance,
                SphinxTx::LOCATOR.bold()
            );
        }

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();
        // Initialize the VM.
        let store = ConsensusStore::<N, ConsensusMemory<N>>::open(None)?;
        let vm: VM<N, ConsensusMemory<N>> = VM::from(store.clone())?;

        // Compute the execution.
        vm.execute_authorization_raw(authorization, Some(query.clone()), rng)
    }

    pub fn gen_fee_authorization<N: Network>(
        private_key: &str,
        execution: Execution<N>,
    ) -> Result<Authorization<N>> {
        // Initialize an RNG.
        let rng = &mut rand::thread_rng();
        // Initialize the VM.
        let store = ConsensusStore::<N, ConsensusMemory<N>>::open(None)?;
        let vm: VM<N, ConsensusMemory<N>> = VM::from(store.clone())?;

        let (minimum_execution_cost, (_, _)) = execution_cost::<N>(&vm.process().read(), &execution)?;

        // Compute the execution ID.
        let execution_id = execution.to_execution_id()?;
        let private_key = PrivateKey::from_str(private_key)?;
        vm.authorize_fee_public(&private_key, minimum_execution_cost, 0, execution_id, rng)
    }

    pub fn broadcast_transaction<N: Network>(
        endpoint: &str,
        authorization: Authorization<N>,
        execution: Execution<N>,
    ) -> Result<String> {
        let net_name = SphinxTx::get_url_prefix::<N>()?;
        let query_url = format!("{}/{}/transaction/broadcast", endpoint, net_name);
        // Specify the query
        let query = Query::from(endpoint);

        // Initialize an RNG.
        let rng = &mut rand::thread_rng();
        // Initialize the VM.
        let store = ConsensusStore::<N, ConsensusMemory<N>>::open(None)?;
        let vm: VM<N, ConsensusMemory<N>> = VM::from(store.clone())?;

        // Execute the fee.
        let fee = Some(vm.execute_fee_authorization_raw(authorization, Some(query.clone()), rng)?);

        // Return the execute transaction.
        let transaction = Transaction::from_execution(execution, fee)?;

        // Get the transaction id.
        let transaction_id = transaction.id();

        // Ensure the transaction is not a fee transaction.
        ensure!(!transaction.is_fee(), "The transaction is a fee transaction and cannot be broadcast");
        if let Transaction::Execute(..) = transaction {
            match ureq::post(&query_url).send_json(&transaction) {
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

    pub fn sync_transaction<N: Network>(endpoint: &str, transaction_id: String) -> Result<bool> {
        let net_name = SphinxTx::get_url_prefix::<N>()?;
        let query_url = format!("{}/{}", endpoint, net_name);

        match ureq::get(&format!("{query_url}/transaction/{transaction_id}")).call() {
            Ok(resp) => {
                let resp_text = resp.status_text().to_string();
                if !resp_text.contains("OK") {
                    return Ok(false);
                }
            }
            Err(error) => {
                bail!(error.to_string())
            }
        }

        match ureq::get(&format!("{query_url}/transaction/confirmed/{transaction_id}")).call() {
            Ok(resp) => {
                let resp_text = resp.status_text().to_string();
                if resp_text.contains("\"status\": \"accepted\"") {
                    return Ok(true);
                }else if resp_text.contains("\"status\": \"rejected\"")  {
                    bail!("transaction is rejected")
                }else{
                    return Ok(false);
                }
            }
            Err(error) => {
                bail!(error.to_string())
            }
        }
    }

    /// Fetch the public balance in microcredits associated with the address from the given endpoint.
    pub fn get_public_balance<N: Network>(from: &str, endpoint: &str) -> Result<u64> {
        let net_name = SphinxTx::get_url_prefix::<N>()?;
        let address = Address::<N>::from_str(from)?;
        // Send a request to the query node.
        let response = ureq::get(&format!("{endpoint}/{net_name}/program/credits.aleo/mapping/account/{address}")).call();

        // Deserialize the balance.
        let balance: Result<Option<Value<N>>> = match response {
            Ok(response) => response.into_json().map_err(|err| err.into()),
            Err(err) => match err {
                ureq::Error::Status(_status, response) => {
                    bail!(response.into_string().unwrap_or("Response too large!".to_owned()))
                }
                err => bail!(err),
            },
        };

        // Return the balance in microcredits.
        match balance {
            Ok(Some(Value::Plaintext(Plaintext::Literal(Literal::<N>::U64(amount), _)))) => Ok(*amount),
            Ok(None) => Ok(0),
            Ok(Some(..)) => bail!("Failed to deserialize balance for {address}"),
            Err(err) => bail!("Failed to fetch balance for {address}: {err}"),
        }
    }

    pub fn get_url_prefix<N:Network>()->Result<String>{
        // Get the network being used.
        let network = match N::ID {
            snarkvm::console::network::MainnetV0::ID => "mainnet",
            snarkvm::console::network::TestnetV0::ID => "testnet",
            snarkvm::console::network::CanaryV0::ID => "canary",
            unknown_id => bail!("Unknown network ID ({unknown_id})"),
        };
        Ok(network.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{thread, time};
    // use snarkvm::prelude::TestnetV0;
    use snarkvm::prelude::MainnetV0;
    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_sphinx_tx() {
        fn _test_sphinx_tx() -> Result<String> {
            let endpoint = "http://127.0.0.1:3030";
            let private_key = "APrivateKey1zkp8CZNn3yeCseEtxuVPbDCwSyhGW6yZKUYKfgXmcpoGPWH";
            let from: &str = "aleo1rhgdu77hgyqd3xjj8ucu3jj9r2krwz6mnzyd80gncr5fxcwlh5rsvzp9px";
            let to: &str = "aleo15mqx2nkc3dzwxknlcxc7pava80vm4cxs5grzf77jkl7xp9vfnqys8cc7hu";
            let amount = "500000001u64";

            let authorization = SphinxTx::gen_tx_authorization::<CurrentNetwork>(private_key, to, amount)?;

            let serialized = serde_json::to_string(&authorization).unwrap();
            let authorization = serde_json::from_str(&serialized).unwrap();

            let execution = SphinxTx::gen_tx_execution::<CurrentNetwork>(endpoint, from, authorization)?;

            let serialized = serde_json::to_string(&execution).unwrap();
            let execution: Execution<CurrentNetwork> = serde_json::from_str(&serialized).unwrap();

            let authorization = SphinxTx::gen_fee_authorization(private_key, execution.clone())?;

            let serialized = serde_json::to_string(&authorization).unwrap();
            let authorization = serde_json::from_str(&serialized).unwrap();

            let transaction_id = SphinxTx::broadcast_transaction(endpoint, authorization, execution)?;

            let mut index = 0;
            while index < 5 {
                index += 1;
                let resp = SphinxTx::sync_transaction::<CurrentNetwork>(endpoint, transaction_id.to_string())?;
                if resp{
                    break;
                }
                thread::sleep(time::Duration::from_secs(30))
            }

            Ok(transaction_id.to_string())
        }

        let ret = _test_sphinx_tx();
        match ret {
            Ok(ret) => println!("ok {ret}"),
            Err(e) =>  println!("err {e}"),
        }

    }

    #[test]
    fn test_new_account_with_seed() {
        let seed = Some("38868010450269069756484274649022187108349082664538872491798902858296683054657".to_string());

        let expected_pri = String::from("APrivateKey1zkp61PAYmrYEKLtRWeWhUoDpFnGLNuHrCciSqN49T86dw3p");
        let expected_view = String::from("AViewKey1eYEGtb78FVg38SSYyzAeXnBdnWCba5t5YxUxtkTtvNAE");
        let expected_pub = String::from("aleo1zecnqchckrzw7dlsyf65g6z5le2rmys403ecwmcafrag0e030yxqrnlg8j");

        let acc = super::new_account::<CurrentNetwork>(seed).unwrap();
        assert_eq!(acc.private_key().to_string(), expected_pri);
        assert_eq!(acc.view_key().to_string(), expected_view);
        assert_eq!(acc.address().to_string(), expected_pub);
    }

    #[test]
    fn test_new_account_without_seed() {
        let acc = super::new_account::<CurrentNetwork>(None).unwrap();
        assert_eq!(acc.private_key().to_string().len(), 59);
        assert_eq!(acc.view_key().to_string().len(), 53);
        assert_eq!(acc.address().to_string().len(), 63);
    }
}
