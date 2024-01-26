forbid(
  principal == a::"&6",
  action,
  resource is a in a::"&6"
) when {
  true && ((if (principal in principal) then resource else principal) is a)
};
