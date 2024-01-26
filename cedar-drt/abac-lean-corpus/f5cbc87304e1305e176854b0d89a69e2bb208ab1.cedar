forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  true && ((if principal then {"_hhh": principal, "A": principal} else principal) == principal)
};
