permit(
  principal,
  action in [Action::"j;jj",Action::"h",Action::""],
  resource
) when {
  true && [!((principal["\t\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0@\0\0\0\0\0\0\0\0\0\0\0\0\0"]) <= principal), principal]
};
