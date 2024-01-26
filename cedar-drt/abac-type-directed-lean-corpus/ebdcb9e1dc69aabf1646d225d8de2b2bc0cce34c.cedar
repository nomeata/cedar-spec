forbid(
  principal == a::"",
  action == Action::"++++",
  resource == a::""
) when {
  true && ((Action::"++++++++++++++" in (resource["Bsss"])) && (a::"" in (principal["Bsss"])))
};
