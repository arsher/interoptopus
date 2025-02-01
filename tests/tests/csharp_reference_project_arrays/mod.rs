use anyhow::Error;
use interoptopus::Interop;
use interoptopus_backend_csharp::{ConfigBuilder, Generator, WriteTypes};
use interoptopus_reference_project::ffi_inventory;
use tests::backend_csharp::{common_namespace_mappings, run_dotnet_command_if_installed};
use tests::validate_output;

#[test]
fn reference_project_with_non_unrolled_arrays() -> Result<(), Error> {
    let config_common = ConfigBuilder::default()
        .namespace_id("common".to_string())
        .unroll_struct_arrays(false)
        .namespace_mappings(common_namespace_mappings())
        .dll_name("interoptopus_reference_project".to_string())
        .write_types(WriteTypes::NamespaceAndInteroptopusGlobal)
        .build()?;

    let config_other = ConfigBuilder::default()
        .namespace_mappings(common_namespace_mappings())
        .unroll_struct_arrays(false)
        .dll_name("interoptopus_reference_project".to_string())
        .write_types(WriteTypes::Namespace)
        .build()?;

    let generated_common = Generator::new(config_common, ffi_inventory()).write_string()?;
    let generated_other = Generator::new(config_other, ffi_inventory()).write_string()?;

    validate_output!("tests/csharp_reference_project_arrays", "Interop.common.cs", generated_common.as_str());
    validate_output!("tests/csharp_reference_project_arrays", "Interop.cs", generated_other.as_str());

    run_dotnet_command_if_installed("tests/csharp_reference_project_arrays", "test")?;

    Ok(())
}
