

# Passes
- finalize_instruction_selection
- discard_alloc_info

# Design Considerations

## Register Allocation Finalization

Right now we finalize instruction selection before we finalize locations, which
means we technically can end up in a situation where the offset can be a
variable that does not become a register, which we'll detect during location
finalization.  If we postponed instruction finalization until *after* location
finalization, however, we'd find it during that pass. The difference would be
that the `mset` and `mref` forms would carry `triv` arguments for longer. It's
unclear if this has any advantage (though it allows us to use `alloc_lang` for
our location finalization input).
