# FAQ


## Misc

- **Why do I get `error[E0658]: macro attributes in #[derive] output are unstable`?**

  This happens when `#[ffi_type]` appears after `#derive[...]`. Just switch their order.


- **How do I support a new language?**

  1) create a new crate, like `my_language`
  1) check which existing backend comes closest, copy that code
  1) start from trait `Interop::write_to` producing some output, fix errors as they appear
  1) create a UI test against `interoptopus_reference_project` to ensure your bindings are stable


- **How does it actually work?**

  As  [answered by Alex Hirsekorn](https://www.quora.com/How-does-an-octopus-eat-a-crab-without-getting-cuts?share=1):
  - When a GPO [Giant Pacific Octopus] finds a crab it does something called a “flaring web-over” which uses the webbing between the arms to engulf the crab while simultaneously immobilizing the crab’s claws with its suckers.
  - With the crab in what amounts to a sealed bag the GPO spits one of its two types of saliva into that space. This first saliva is called cephalotoxin and acts as a sedative, rendering the crab unconscious but still alive. [If the crab is taken away from the GPO at this point it will wake up and run away.]
  - The GPO then spits the other kind of saliva into the crab; that saliva is a powerful digestive enzyme. Since the crab is still alive at this point it pumps that enzyme throughout its body and basically digests itself on the GPO’s behalf. The octopus typically takes a nap during this stage.
  - After some period of time (I’ve seen this vary from 1.5 to 3 hours) the GPO wakes up, disassembles the crab, and licks out what amounts to crab meat Jell-O with a tongue-like structure called a radula. As Kathleen said the GPO does the disassembly with its suckers but it doesn’t just open the carapace: It will also take the claws and legs apart at the various joints.
  - When the meal is finished and the shell parts tossed out the GPO will take another nap until it’s hungry again. [Studies have shown that a GPO spends as much as 70% of its time sleeping in its den.]

  Occasionally a GPO will get minor injuries from capturing the crab but, for the most part they are too careful and too skilled for that to be much of an issue.

  After the GPO has rested, FFI bindings are produced.


## Safety, Soundness, Undefined Behavior

This library naturally does "unsafe" things and any journey into FFI-land is a little adventure.
That said, here are some assumptions and quality standards this project is based on:

- Safe Rust calling safe Rust code must always be sound, with soundness boundaries
on the module level, although smaller scopes are preferred. For example, creating a `FFISlice`
from Rust and directly using it from Rust must never cause UB.

- We must never willingly generate broken bindings. For _low level types_ we must never
generate bindings which "cannot be used correctly" (e.g., map a `u8` to a `float`), for
_patterns_ we must generate bindings that are "correct if used according to specification".

- There are situations where the (Rust) soundness of a binding invocation depends on conditions outside
our control. In these cases we trust foreign code will invoke the generated functions
correctly. For example, if a function is called with an `AsciiPointer` type we consider it _safe and sound_
to obtain a `str` from this pointer as `AsciiPointer`'s contract specifies it must point to
ASCII data.

- Related to the previous point we generally assume functions and types on both sides are used _appropriately_ w.r.t.
Rust's FFI requirements and we trust you do that, e.g., you must declare types `#[repr(C)]` (or similar)
and functions `extern "C"`.

- Any `unsafe` code in any abstraction we provide should be "well contained", properly documented
and reasonably be auditable.

- If unsound Rust types or bindings were ever needed (e.g., because of a lack of Rust specification,
like 'safely' mapping a trait's vtable) such bindings should be gated behind a feature flag
(e.g., `unsound`) and only enabled via an explicit opt-in. Right now there are none, but this is
to set expectations around discussions.


## Licensing

A clarification how the license is meant to be applied:

- Our license only applies to code **in** this repository, not code generated **by** this repository.
  
- We do not claim copyright for code produced by backends included here; even if said code was based on a template in this repository. 
  
- For the avoidance of doubt, anything produced by `Interop::write_to` or any item emitted by a proc macro is considered “generated by”.