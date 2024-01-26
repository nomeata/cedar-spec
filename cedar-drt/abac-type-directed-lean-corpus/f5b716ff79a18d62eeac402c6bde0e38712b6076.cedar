@A338knj("at")
@r("")
forbid(
  principal in a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  true && (({"": []}[""]).containsAny([]))
};
