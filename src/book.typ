#import "common.typ": *

#show: marginalia.setup.with(
// inner: ( far: 5mm, width: 50mm, sep: 5mm ),
outer: ( far: 5mm, width: 50mm, sep: 5mm ),
// top: 2.5cm,
// bottom: 2.5cm,
book: false,
// clearance: 12pt,
)

#show: init-color-my-agda
#import "@preview/ilm:3.0.0": *

#set text(lang: "en")

#show: ilm.with(
  title: [A good title],
  authors: "Αποστόλης Ξεκουκουλωτάκης" ,
  date: datetime.today()
)

#cover-page()

#outline()

#include "Introduction.typ"
#include "TheoryAndPractice.typ"
#include "InformalModel.typ"
#include "CompositionLevels.typ"

#bibliography("bibliography.bib")
