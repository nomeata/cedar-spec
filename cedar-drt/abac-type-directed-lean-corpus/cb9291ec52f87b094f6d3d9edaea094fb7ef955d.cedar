forbid(
  principal is a in a::"",
  action in [Action::"++++++++++++++++++++++++"],
  resource == a::""
) when {
  ((true && (action in [action])) && ((false && (action in [])) && (a::"" in (principal["Bsss"])))) && (principal in [])
};
