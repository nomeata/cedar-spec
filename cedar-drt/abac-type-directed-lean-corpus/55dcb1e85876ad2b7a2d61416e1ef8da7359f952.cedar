forbid(
  principal == a::"&6",
  action,
  resource is a in a::"&6"
) when {
  true && (resource is a)
};
