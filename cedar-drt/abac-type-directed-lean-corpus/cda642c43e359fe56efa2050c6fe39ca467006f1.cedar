permit(
  principal == a::"6$",
  action,
  resource in a::"6$"
) when {
  true && (a::"6$" in ({"st": []}["st"]))
};
